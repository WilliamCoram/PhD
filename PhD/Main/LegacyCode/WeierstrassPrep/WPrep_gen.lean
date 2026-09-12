import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.Module.FiniteDimension
import PhD.WeierstrassPrep.WPrep

-- see `PhD/ToPR/RestrictedIso.lean`: needed since the v4.33 bump for the `Restricted`
-- `Subring.toRing`/`toCommRing` instance diamond.
set_option backward.isDefEq.respectTransparency false

/-!
# Weierstrass division and preparation at a general Gauss-norm parameter (roadmap)

`WeierstrassDivision.lean` and `WPrep.lean` prove Weierstrass division and preparation for the
restricted power series ring `PowerSeries.Restricted R 1` — Gauss-norm parameter `c = 1`.  The
Newton-polygon theory (`PhD/Main/Test/test.lean`) consumes them at the *slope radii* `c = exp m`,
which over `ℚ_p` are values like `p^(1/2)`: not norms of elements of the field, but with a
power that is.  This file sets out the generalisation to every `c` in the **divisible closure
of the value group**, in three rungs.

* **Rung 1 (rescaling): `c` the norm of a unit.**  For a unit `u` with `‖u‖ = c`, the
  substitution `x ↦ ux` — Mathlib's `PowerSeries.rescale u`, coefficientwise `aₖ ↦ uᵏ aₖ`
  (`PowerSeries.coeff_rescale`) — is an isometric ring isomorphism
  `Restricted R c ≃+* Restricted R 1`: the `k`-th Gauss term `‖aₖ‖ cᵏ` at parameter `c` becomes
  `‖uᵏ aₖ‖ · 1ᵏ` at parameter `1`, so Gauss norms and the `distinguished` structure match on
  the nose.  Division and preparation at `c` are then the `c = 1` theorems transported along
  the isomorphism.  (§2, §3.)

* **Rung 2 (finite extension and descent): `cⁿ` the norm of an element.**  Over a *complete*
  ultrametric field `K` with `‖x‖ = cⁿ`, the finite extension `L = K(α)` with `αⁿ = x` carries
  a unique complete ultrametric norm extending that of `K` — the spectral norm; see
  `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` and its neighbours for the
  norm-extension theory.  In `L` we have `‖α‖ⁿ = ‖x‖ = cⁿ`, hence `‖α‖ = c`, and rung 1
  applies over `L`.  The division/preparation of data defined over `K` then **descends** to
  `K` by uniqueness: decompose `L`-restricted series along a `K`-basis of `L` with `b₀ = 1`
  (all norms on a finite-dimensional space over a complete field are equivalent, so the
  components of a restricted series are restricted); the `b₀`-component of the `L`-division of
  a `K`-element is itself a `K`-division, and the division bounds applied to the remaining
  components (divisions of `0`) force them to vanish.  No Galois theory and no separability is
  needed for this argument.  (§4, §5 — stated there in one variable over a field; see the
  generality note at the head of §4: the eventual home of rung 2 is `MvRestricted` over a
  complete field bottom, so that bases `R = Restricted S` (Tate algebras) are covered via
  `RestrictedIso`, exactly as at `c = 1`.)

* **Rung 3 (limits): every `c > 0` — not pursued.**  The divisible closure of a nontrivial
  value group is dense in `(0, ∞)`, so a limiting argument along good radii would remove the
  divisibility hypothesis altogether.  Nothing in the Newton-polygon theory needs this: slope
  radii always lie in the divisible closure
  (`NewtonPolygon.memDivisibleValueGroup_exp_slope` in `PhD/Main/Test/test.lean`).

## The `distinguished` predicate at a general parameter

The imported `distinguished v c f s` is `c = 1`-normalised: its norm conditions compare the
plain values `v (coeff t f)` with no `c ^ t` weights.  This file first introduces the
corrected predicate `distinguishedGen` (§0), which weights the `t`-th coefficient by `c ^ t`,
agrees with `distinguished` at `c = 1`, and is what rescaling transports; all statements
below use it.

## Caution: completeness is essential, not incidental

Over the *incomplete* field `ℚ` with the `5`-adic norm, `f = X² − 5X + 125` is irreducible
(negative discriminant), yet its Newton polygon has two slopes, so the Weierstrass factor at
the smaller slope radius would be linear — no such factor exists in `ℚ[X]`.  Equivalently: the
extension of the norm to the algebraic closure of an incomplete field is not unique, so "the
factor collecting the roots of norm `≤ c`" is not Galois-stable and need not descend.  All
rung-2 statements below therefore assume `[CompleteSpace K]`, and the consumer
`NewtonPolygon.exists_factor_of_distinguished` in `PhD/Main/Test/test.lean` — currently stated
without completeness — **must gain `[CompleteSpace K]`** when it is discharged from this file.

## Status

**Complete — no `sorry`.**  Signatures mirror those of
`WeierstrassDivision.lean`/`WPrep.lean` (`PowerSeries.Restricted`, `distinguishedGen norm c`,
the `h`/`hunit` scaling hypotheses) with `1` replaced by `c`.  Naming: rung-1/ring-level
generalisations carry the suffix `_gen`; rung-2/field endpoints carry `_divisible`.  The
finite extension of rung 2 is realised inside `AlgebraicClosure K` as `K⟮α⟯` with Mathlib's
spectral norm (`spectralNorm.nontriviallyNormedField`).  The `c = 1` results are now the
special case `u = 1` of the `_gen` versions; whether to refactor the original files down to
that is a later decision.
-/

open Topology

/-! ## §0  The `distinguished` predicate at a general parameter

`WeierstrassDivision.lean`'s `distinguished v c f s` is normalised at `c = 1`: its fields
compare the plain values `v (coeff t f)` with **no `c ^ t` weights** — invisible at `c = 1`,
wrong at a general parameter, where the Gauss term of the `t`-th coefficient is
`v (coeff t f) * c ^ t`.  (With the unweighted predicate, no nonconstant monic polynomial
could be distinguished at a parameter `c ≠ 1` however dominant its top Gauss term.)
`distinguishedGen` is the corrected predicate: it agrees with `distinguished` at `c = 1`
(`distinguishedGen_one_iff`) and corresponds to it along rescaling
(`distinguished_rescaleEquiv`, §2).  All `_gen`/`_divisible` statements below use it.  When
the `c = 1` files are eventually refactored, `distinguished` itself can be redefined this
way. -/

section DistinguishedGen

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R) (s : ℕ)

/-- `f` is **distinguished of degree `s` at parameter `c`**: the `s`-th coefficient is a
unit, its Gauss term attains the Gauss norm, and it strictly dominates every later Gauss
term.  Generalises `distinguished` (recovered at `c = 1`, see `distinguishedGen_one_iff`) by
weighting the `t`-th coefficient with `c ^ t`. -/
structure distinguishedGen : Prop where
  unit : IsUnit (PowerSeries.coeff s f)
  norm_eq : PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f) * c ^ s
  norm_max : ∀ t, s < t → v (PowerSeries.coeff t f) * c ^ t < v (PowerSeries.coeff s f) * c ^ s

variable {v c f s}

/-- At `c = 1` the corrected predicate is the original one. -/
lemma distinguishedGen_one_iff : distinguishedGen v 1 f s ↔ distinguished v 1 f s := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · show PowerSeries.gaussNorm v 1 f = v (PowerSeries.coeff s f)
      simpa using h2
    · show ∀ t, s < t → v (PowerSeries.coeff t f) < v (PowerSeries.coeff s f)
      intro t ht
      simpa using h3 t ht
  · rintro ⟨h1, h2, h3⟩
    have h2' : PowerSeries.gaussNorm v 1 f = v (PowerSeries.coeff s f) := h2
    have h3' : ∀ t, s < t → v (PowerSeries.coeff t f) < v (PowerSeries.coeff s f) := h3
    exact ⟨h1, by simpa using h2', fun t ht => by simpa using h3' t ht⟩

/-- A `distinguishedGen` series is nonzero (cf. `distinguished.ne_zero`). -/
lemma distinguishedGen.ne_zero [Nontrivial R] (hg : distinguishedGen v c f s) : f ≠ 0 :=
  fun h0 => hg.unit.ne_zero (by rw [h0, map_zero])

end DistinguishedGen

section GeneralParameter

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R]
  [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R]

variable {c : ℝ} [StrongPos (fun _ : Unit ↦ c)]

/-! ## §1  Infrastructure at parameter `c`

The `local instance`s of `WPrep.lean` for `Restricted R 1`, generalised to `Restricted R c`.
Positivity of `c` enters only through the `StrongPos (fun _ : Unit ↦ c)` instance-hypothesis
(recover `0 < c` via `StrongPos_pos`). -/

-- The Gauss-norm instances on `Restricted R c` require `StrongPos (fun _ ↦ c)`; the section
-- variable supplies it at `c`, and (as in WPrep.lean) we supply it at the rescaling target `1`.
local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) := ⟨fun _ ↦ one_pos⟩

local instance : NormMulClass (PowerSeries.Restricted R c) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ c)

local instance : NormOneClass (PowerSeries.Restricted R c) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) c, PowerSeries.Restricted.norm_C, norm_one]

-- Note: WPrep.lean additionally installs `Filter.NeBot (𝓝[≠] (0 : Restricted R 1))` for its
-- power-bounded/residue machinery.  No analogue is needed at parameter `c`: everything below
-- is obtained from the `c = 1` results by transport and descent, never by re-running that
-- machinery.

/-! ## §2  Rescaling (rung 1): the isometry `Restricted R c ≃+* Restricted R 1`

The underlying map is `PowerSeries.rescale (u : R)`, i.e. `x ↦ ux` on series,
`aₖ ↦ uᵏ aₖ` on coefficients; its inverse is `PowerSeries.rescale ((u⁻¹ : Rˣ) : R)`.
Well-definedness (restricted ↦ restricted) is the computation `‖uᵏ aₖ‖ · 1ᵏ = ‖aₖ‖ cᵏ`, which
needs `NormMulClass R` and `‖u‖ = c`. -/

section Rescale

omit [IsUltrametricDist R] [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- Rescaling by `a` carries series restricted at `c₁` to series restricted at `c₂` whenever
`‖a‖ * c₂ = c₁`: the `k`-th Gauss terms are then equal. -/
private lemma isRestricted_rescale {c₁ c₂ : ℝ} (a : R) (ha : ‖a‖ * c₂ = c₁)
    {f : PowerSeries R} (hf : PowerSeries.IsRestricted c₁ f) :
    PowerSeries.IsRestricted c₂ (PowerSeries.rescale a f) := by
  rw [PowerSeries.isRestricted_iff] at hf ⊢
  refine hf.congr fun k => ?_
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, ← ha, mul_pow]
  ring

omit [IsUltrametricDist R] [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma norm_units_inv (u : Rˣ) (hu : ‖(u : R)‖ = c) :
    ‖((u⁻¹ : Rˣ) : R)‖ = c⁻¹ := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  have h1 : ‖(u : R) * ((u⁻¹ : Rˣ) : R)‖ = 1 := by rw [Units.mul_inv]; exact norm_one
  rw [norm_mul, hu] at h1
  exact mul_left_cancel₀ hc0.ne' (by rw [h1, mul_inv_cancel₀ hc0.ne'])

/-- **Rescaling as a ring isomorphism** `Restricted R c ≃+* Restricted R 1`: the substitution
`x ↦ ux` on series, `aₖ ↦ uᵏ aₖ` on coefficients (Mathlib's `PowerSeries.rescale`), with
inverse `x ↦ u⁻¹x`. -/
noncomputable def Restricted.rescaleEquiv (u : Rˣ) (hu : ‖(u : R)‖ = c) :
    PowerSeries.Restricted R c ≃+* PowerSeries.Restricted R 1 where
  toFun f := ⟨PowerSeries.rescale (u : R) f.1,
    isRestricted_rescale (u : R) (by rw [hu, mul_one]) f.2⟩
  invFun g := ⟨PowerSeries.rescale ((u⁻¹ : Rˣ) : R) g.1,
    isRestricted_rescale ((u⁻¹ : Rˣ) : R)
      (by rw [norm_units_inv u hu,
        inv_mul_cancel₀ (StrongPos_pos (fun _ : Unit ↦ c) ()).ne']) g.2⟩
  left_inv f := Subtype.ext <| by
    show PowerSeries.rescale _ (PowerSeries.rescale _ f.1) = f.1
    rw [PowerSeries.rescale_rescale, Units.mul_inv, PowerSeries.rescale_one, RingHom.id_apply]
  right_inv g := Subtype.ext <| by
    show PowerSeries.rescale _ (PowerSeries.rescale _ g.1) = g.1
    rw [PowerSeries.rescale_rescale, Units.inv_mul, PowerSeries.rescale_one, RingHom.id_apply]
  map_mul' f g := Subtype.ext <| by
    show PowerSeries.rescale (u : R) (f.1 * g.1) = _
    exact map_mul (PowerSeries.rescale (u : R)) f.1 g.1
  map_add' f g := Subtype.ext <| by
    show PowerSeries.rescale (u : R) (f.1 + g.1) = _
    exact map_add (PowerSeries.rescale (u : R)) f.1 g.1

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- The underlying power series of a rescaling is `PowerSeries.rescale`. -/
lemma Restricted.rescaleEquiv_coe (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (f : PowerSeries.Restricted R c) :
    (Restricted.rescaleEquiv u hu f).1 = PowerSeries.rescale (u : R) f.1 := rfl

omit [IsUltrametricDist R] [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R]
  [StrongPos (fun _ : Unit ↦ c)] in
/-- The Gauss norm at parameter `1` of a rescaled series is the Gauss norm at parameter `c`
of the original: term by term, `‖uᵏ aₖ‖ · 1ᵏ = ‖aₖ‖ cᵏ`. -/
private lemma gaussNorm_rescale (u : Rˣ) (hu : ‖(u : R)‖ = c) (f : PowerSeries R) :
    PowerSeries.gaussNorm norm 1 (PowerSeries.rescale (u : R) f)
      = PowerSeries.gaussNorm norm c f := by
  rw [PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  refine iSup_congr fun k => ?_
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, hu, one_pow, mul_one, mul_comm]

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- Rescaling is a **Gauss-norm isometry**.  (This is what carries the bounds on `q` and `r`
across the isomorphism.) -/
lemma Restricted.norm_rescaleEquiv (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (f : PowerSeries.Restricted R c) :
    ‖Restricted.rescaleEquiv u hu f‖ = ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, Restricted.rescaleEquiv_coe]
  exact gaussNorm_rescale u hu f.1

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- Rescaling matches `distinguished` at parameter `1` with `distinguishedGen` at parameter
`c`: multiplication by the unit `uᵏ` preserves unit coefficients, and the Gauss terms
correspond, so attainment and strict domination of the norm correspond. -/
lemma distinguished_rescaleEquiv (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (f : PowerSeries.Restricted R c) (s : ℕ) :
    distinguished norm 1 (Restricted.rescaleEquiv u hu f).1 s ↔
      distinguishedGen norm c f.1 s := by
  rw [Restricted.rescaleEquiv_coe]
  have hcoeff : ∀ k, ‖PowerSeries.coeff k (PowerSeries.rescale (u : R) f.1)‖
      = ‖PowerSeries.coeff k f.1‖ * c ^ k := fun k => by
    rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, hu, mul_comm]
  have hunit : ∀ k, IsUnit (PowerSeries.coeff k (PowerSeries.rescale (u : R) f.1))
      ↔ IsUnit (PowerSeries.coeff k f.1) := fun k => by
    rw [PowerSeries.coeff_rescale, ← Units.val_pow_eq_pow_val, Units.isUnit_units_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h2' : PowerSeries.gaussNorm norm 1 (PowerSeries.rescale (u : R) f.1)
        = ‖PowerSeries.coeff s (PowerSeries.rescale (u : R) f.1)‖ := h2
    have h3' : ∀ t, s < t → ‖PowerSeries.coeff t (PowerSeries.rescale (u : R) f.1)‖
        < ‖PowerSeries.coeff s (PowerSeries.rescale (u : R) f.1)‖ := h3
    refine ⟨(hunit s).mp h1, ?_, fun t ht => ?_⟩
    · rw [← gaussNorm_rescale u hu f.1, h2', hcoeff s]
    · have := h3' t ht
      rwa [hcoeff t, hcoeff s] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsUnit (PowerSeries.coeff s (PowerSeries.rescale (u : R) f.1))
      exact (hunit s).mpr h1
    · show PowerSeries.gaussNorm norm 1 (PowerSeries.rescale (u : R) f.1)
        = ‖PowerSeries.coeff s (PowerSeries.rescale (u : R) f.1)‖
      rw [gaussNorm_rescale u hu f.1, hcoeff s, h2]
    · show ∀ t, s < t → ‖PowerSeries.coeff t (PowerSeries.rescale (u : R) f.1)‖
        < ‖PowerSeries.coeff s (PowerSeries.rescale (u : R) f.1)‖
      intro t ht
      rw [hcoeff t, hcoeff s]
      exact h3 t ht

omit [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma coeff_comp_C_mul_X (p : Polynomial R) (a : R) (k : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff k = a ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b =>
    rw [Polynomial.monomial_comp, mul_pow, ← map_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, mul_ite, mul_zero]
    split_ifs with h
    · subst h
      exact mul_comm b (a ^ n)
    · rfl

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- Rescaling sends polynomials to polynomials: `ω(x) ↦ ω(ux)`. -/
lemma Restricted.rescaleEquiv_toRestricted (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (ω : Polynomial R) :
    Restricted.rescaleEquiv u hu (Polynomial.toRestricted c ω)
      = Polynomial.toRestricted 1 (ω.comp (Polynomial.C (u : R) * Polynomial.X)) := by
  refine Subtype.ext ?_
  show PowerSeries.rescale (u : R) (ω : PowerSeries R)
      = ((ω.comp (Polynomial.C (u : R) * Polynomial.X) : Polynomial R) : PowerSeries R)
  ext k
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe,
    coeff_comp_C_mul_X]

omit [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma comp_C_mul_X_cancel (p : Polynomial R) (u : Rˣ) :
    (p.comp (Polynomial.C (u : R) * Polynomial.X)).comp
      (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X) = p := by
  ext k
  rw [coeff_comp_C_mul_X, coeff_comp_C_mul_X, ← mul_assoc, ← mul_pow, Units.inv_mul,
    one_pow, one_mul]

omit [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma comp_C_mul_X_cancel' (p : Polynomial R) (u : Rˣ) :
    (p.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)).comp
      (Polynomial.C (u : R) * Polynomial.X) = p := by
  have h := comp_C_mul_X_cancel p u⁻¹
  rwa [inv_inv] at h

omit [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma degree_comp_C_mul_X_lt {r : Polynomial R} {s : ℕ}
    (hr : r.degree < s) (a : R) :
    (r.comp (Polynomial.C a * Polynomial.X)).degree < s := by
  rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
  intro m hm
  rw [coeff_comp_C_mul_X, hr m hm, mul_zero]

omit [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
private lemma degree_comp_C_mul_X_le_of {r : Polynomial R} {s : ℕ}
    (hr : r.degree ≤ (s : WithBot ℕ)) (a : R) :
    (r.comp (Polynomial.C a * Polynomial.X)).degree ≤ (s : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero] at hr ⊢
  intro m hm
  rw [coeff_comp_C_mul_X, hr m hm, mul_zero]

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- The inverse rescaling also sends polynomials to polynomials: `r(x) ↦ r(u⁻¹x)`. -/
lemma Restricted.rescaleEquiv_symm_toRestricted (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (r : Polynomial R) :
    (Restricted.rescaleEquiv u hu).symm (Polynomial.toRestricted 1 r)
      = Polynomial.toRestricted c
          (r.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) := by
  rw [RingEquiv.symm_apply_eq, Restricted.rescaleEquiv_toRestricted, comp_C_mul_X_cancel']

omit [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- The scaling hypothesis `hunit` at parameter `c` transports to parameter `1` along the
(isometric) rescaling. -/
private lemma hunit_transport (u : Rˣ) (hu : ‖(u : R)‖ = c)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a := by
  intro f' hf'
  have hne : (Restricted.rescaleEquiv u hu).symm f' ≠ 0 := fun h0 => hf' (by
    have h := congrArg (Restricted.rescaleEquiv u hu) h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at h)
  have h := hunit ((Restricted.rescaleEquiv u hu).symm f') hne
  rwa [← Restricted.norm_rescaleEquiv u hu ((Restricted.rescaleEquiv u hu).symm f'),
    RingEquiv.apply_symm_apply] at h

end Rescale

/-! ## §3  Division and preparation at `c = ‖unit‖` (rung 1)

Statements mirror `WeierstrassDivision.lean`/`WPrep.lean` verbatim with `1 ↦ c`, with
`distinguished` upgraded to the weighted `distinguishedGen` (§0), plus the rescaling
hypothesis `hα : ∃ u : Rˣ, ‖(u : R)‖ = c`.  Proofs: transport along
`Restricted.rescaleEquiv` (note a monic `ω` of degree `s` at parameter `1` pulls back to
`ω(u⁻¹x)` with leading coefficient `u⁻ˢ`; renormalise by `uˢ` to stay monic, which turns the
norm normalisation `‖ω‖ = 1` into `‖ω‖ = cˢ`).

The bounds and quotient-uniqueness need no unit at all — their `c = 1` proofs are pure norm
estimates (`contra`) — so they are stated for every (strongly) positive `c`; they can be
proved either by rerunning those estimates at `c` or by transport where a unit is present. -/

omit [CompleteSpace R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] in
/-- The core estimate behind the division bounds, generalising `contra`: in a Weierstrass
division `f = g·q + r` at parameter `c`, the norm of `f` cannot undercut both `‖g·q‖` and
`‖r‖`.  The dominant Gauss term of `g·q` sits at index `peak(q) + s`, where `r` has no
coefficient, so it survives into `f`. -/
private lemma contra_gen (g : PowerSeries.Restricted R c) (s : ℕ)
    (hg : distinguishedGen norm c g.1 s) (f q : PowerSeries.Restricted R c) (r : Polynomial R)
    (hr : Polynomial.degree r < s) (hf : f = g * q + Polynomial.toRestricted c r)
    (hf_lt : ‖f‖ < max ‖g * q‖ ‖Polynomial.toRestricted c r‖) : False := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  by_cases hq_zero : q = 0
  · subst hq_zero
    rw [mul_zero, zero_add] at hf
    rw [hf, mul_zero, norm_zero, max_eq_right (norm_nonneg _)] at hf_lt
    exact lt_irrefl _ hf_lt
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq_zero
  -- Gauss-term bounds for `g` and `q`.
  have h_le_q : ∀ a, ‖PowerSeries.coeff a q.1‖ * c ^ a ≤ ‖q‖ := fun a => by
    have := PowerSeries.le_gaussNorm norm c q.1 (Restricted.hasGaussNorm c q) a
    rwa [← Restricted.norm_eq] at this
  have h_le_g : ∀ a, ‖PowerSeries.coeff a g.1‖ * c ^ a ≤ ‖g‖ := fun a => by
    have := PowerSeries.le_gaussNorm norm c g.1 (Restricted.hasGaussNorm c g) a
    rwa [← Restricted.norm_eq] at this
  -- Restrictedness ⇒ the Gauss terms of `q` tend to `0`, so the peak set is finite.
  have h_restr_q : Filter.Tendsto
      (fun a : ℕ => ‖PowerSeries.coeff a q.1‖ * c ^ a) Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff c q.1).mp q.2
    rwa [Nat.cofinite_eq_atTop] at h
  obtain ⟨N, hN⟩ : ∃ N, ∀ a ≥ N, ‖PowerSeries.coeff a q.1‖ * c ^ a < ‖q‖ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr_q ‖q‖ hq_pos
    refine ⟨N, fun a ha => ?_⟩
    have := hN a ha
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_pos hc0 a).le)] at this
  have h_peak_finite : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ * c ^ a = ‖q‖}).Finite := by
    refine Set.Finite.subset (Set.finite_Iio N) (fun a ha => ?_)
    by_contra h_ge
    exact (lt_self_iff_false ‖q‖).mp (ha ▸ hN a (Nat.le_of_not_lt h_ge))
  have h_peak_nonempty : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ * c ^ a = ‖q‖}).Nonempty := by
    obtain ⟨a₀, ha₀⟩ := Restricted.gaussNorm_achieved' c hc0.le q
    refine ⟨a₀, ?_⟩
    show ‖PowerSeries.coeff a₀ q.1‖ * c ^ a₀ = ‖q‖
    rw [ha₀]; rfl
  -- Take the largest peak `u`.
  let M_set := h_peak_finite.toFinset
  have hM_ne : M_set.Nonempty := by rw [Set.Finite.toFinset_nonempty]; exact h_peak_nonempty
  let u := M_set.max' hM_ne
  have hu_peak : ‖PowerSeries.coeff u q.1‖ * c ^ u = ‖q‖ := by
    have hu_mem := M_set.max'_mem hM_ne
    simp [M_set] at hu_mem; exact hu_mem
  have hu_max : ∀ a, u < a → ‖PowerSeries.coeff a q.1‖ * c ^ a < ‖q‖ := by
    intro a ha_gt
    by_contra h_not_lt
    rw [not_lt] at h_not_lt
    have h_a_in : a ∈ M_set := by
      simp only [M_set, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact le_antisymm (h_le_q a) h_not_lt
    have := M_set.le_max' a h_a_in
    omega
  -- `‖coeff_s g.1‖ · c^s = ‖g‖` and `‖g‖ > 0`.
  have hg_pos : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  have h_coeff_s_g : ‖PowerSeries.coeff s g.1‖ * c ^ s = ‖g‖ := by
    have h := hg.norm_eq
    rw [← h, ← Restricted.norm_eq]
  -- Dominant coefficient: the `(u+s)`-th Gauss term of `g*q` is `‖g‖·‖q‖`.
  have h_peak_gq : ‖PowerSeries.coeff (u + s) (g * q).1‖ * c ^ (u + s) = ‖g‖ * ‖q‖ := by
    show ‖PowerSeries.coeff (u + s) (g.1 * q.1)‖ * c ^ (u + s) = ‖g‖ * ‖q‖
    rw [PowerSeries.coeff_mul]
    have h_su_mem : (s, u) ∈ Finset.antidiagonal (u + s) := by
      rw [Finset.mem_antidiagonal]; ring
    rw [← Finset.sum_erase_add _ _ h_su_mem]
    have h_rest_lt : ∀ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
        ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ * c ^ (u + s) <
          ‖g‖ * ‖q‖ := by
      rintro ⟨a, b⟩ hp
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
      obtain ⟨hne, hmem⟩ := hp
      rw [norm_mul, ← hmem, pow_add,
        show ‖PowerSeries.coeff a g.1‖ * ‖PowerSeries.coeff b q.1‖ * (c ^ a * c ^ b)
          = (‖PowerSeries.coeff a g.1‖ * c ^ a) * (‖PowerSeries.coeff b q.1‖ * c ^ b) from
          by ring]
      rcases lt_trichotomy a s with hlt | heq | hgt
      · have hb_lt : ‖PowerSeries.coeff b q.1‖ * c ^ b < ‖q‖ := hu_max b (by omega)
        calc (‖PowerSeries.coeff a g.1‖ * c ^ a) * (‖PowerSeries.coeff b q.1‖ * c ^ b)
            ≤ ‖g‖ * (‖PowerSeries.coeff b q.1‖ * c ^ b) :=
              mul_le_mul_of_nonneg_right (h_le_g a)
                (mul_nonneg (norm_nonneg _) (pow_pos hc0 b).le)
          _ < ‖g‖ * ‖q‖ := mul_lt_mul_of_pos_left hb_lt hg_pos
      · exact absurd (Prod.ext heq (by simp only; omega)) hne
      · have ha_lt : ‖PowerSeries.coeff a g.1‖ * c ^ a < ‖g‖ := by
          have := hg.norm_max a hgt
          rwa [h_coeff_s_g] at this
        calc (‖PowerSeries.coeff a g.1‖ * c ^ a) * (‖PowerSeries.coeff b q.1‖ * c ^ b)
            ≤ (‖PowerSeries.coeff a g.1‖ * c ^ a) * ‖q‖ :=
              mul_le_mul_of_nonneg_left (h_le_q b)
                (mul_nonneg (norm_nonneg _) (pow_pos hc0 a).le)
          _ < ‖g‖ * ‖q‖ := mul_lt_mul_of_pos_right ha_lt hq_pos
    have h_rest_norm_lt :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
          PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ * c ^ (u + s) <
          ‖g‖ * ‖q‖ := by
      by_cases h_ne_empty : ((Finset.antidiagonal (u + s)).erase (s, u)).Nonempty
      · have hckpos : (0 : ℝ) < c ^ (u + s) := pow_pos hc0 _
        rw [← lt_div_iff₀ hckpos]
        calc ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
              PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖
            ≤ ((Finset.antidiagonal (u + s)).erase (s, u)).sup' h_ne_empty
                (fun p => ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖) :=
              h_ne_empty.norm_sum_le_sup'_norm _
          _ < ‖g‖ * ‖q‖ / c ^ (u + s) := (Finset.sup'_lt_iff h_ne_empty).mpr fun p hp => by
              rw [lt_div_iff₀ hckpos]; exact h_rest_lt p hp
      · rw [Finset.not_nonempty_iff_eq_empty] at h_ne_empty
        rw [h_ne_empty, Finset.sum_empty, norm_zero, zero_mul]
        exact mul_pos hg_pos hq_pos
    have h_peak_norm :
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ * c ^ (u + s) = ‖g‖ * ‖q‖ := by
      rw [norm_mul,
        show ‖PowerSeries.coeff s g.1‖ * ‖PowerSeries.coeff u q.1‖ * c ^ (u + s)
          = (‖PowerSeries.coeff s g.1‖ * c ^ s) * (‖PowerSeries.coeff u q.1‖ * c ^ u) from by
          rw [pow_add]; ring,
        h_coeff_s_g, hu_peak]
    have h_raw_lt :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
          PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ <
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ :=
      lt_of_mul_lt_mul_right (h_rest_norm_lt.trans_eq h_peak_norm.symm)
        (pow_pos hc0 (u + s)).le
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h_raw_lt),
      max_eq_right h_raw_lt.le]
    exact h_peak_norm
  -- `coeff_{u+s} r = 0` since `u + s ≥ s > deg r`.
  have h_toR_zero : PowerSeries.coeff (u + s) (Polynomial.toRestricted c r).1 = 0 := by
    show PowerSeries.coeff (u + s) r.toPowerSeries = 0
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hr.trans_le (by exact_mod_cast Nat.le_add_left s u))
  -- Hence the `(u+s)`-th Gauss term of `f` is `‖g‖·‖q‖`, so `‖g*q‖ ≤ ‖f‖`.
  have h_coeff_f : ‖PowerSeries.coeff (u + s) f.1‖ * c ^ (u + s) = ‖g‖ * ‖q‖ := by
    rw [hf, show (g * q + Polynomial.toRestricted c r).1 =
        (g * q).1 + (Polynomial.toRestricted c r).1 from rfl, map_add, h_toR_zero, add_zero]
    exact h_peak_gq
  have h_gq_bd : ‖g * q‖ ≤ ‖f‖ := by
    rw [norm_mul, ← h_coeff_f]
    have := PowerSeries.le_gaussNorm norm c f.1 (Restricted.hasGaussNorm c f) (u + s)
    rwa [← Restricted.norm_eq] at this
  rcases lt_max_iff.mp hf_lt with h1 | h2
  · exact lt_irrefl _ (h1.trans_le h_gq_bd)
  · have h_toR_bd : ‖Polynomial.toRestricted c r‖ ≤ ‖f‖ := by
      rw [show Polynomial.toRestricted c r = f - g * q from by rw [hf]; abel]
      refine (?_ : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖).trans (max_le le_rfl h_gq_bd)
      have := IsUltrametricDist.norm_add_le_max f (-(g * q))
      rwa [← sub_eq_add_neg, norm_neg] at this
    exact lt_irrefl _ (h2.trans_le h_toR_bd)

omit [CompleteSpace R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] in
lemma weierstrassDivision_bounds_q_gen (g : PowerSeries.Restricted R c) (s : ℕ)
    (hg : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted R c)
    (q : PowerSeries.Restricted R c) (r : Polynomial R) (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted c r)) : ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  by_contra hcon
  have hlt : ‖f‖ < ‖q‖ * ‖g‖ := by
    suffices h : (0 : ℝ) < ‖g‖ by
      have := mul_lt_mul_of_pos_right (not_le.mp hcon) h
      field_simp at this
      simpa [mul_comm]
    exact norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  rw [← norm_mul, mul_comm] at hlt
  exact contra_gen g s hg f q r hr hf (lt_max_iff.mpr (Or.inl hlt))

omit [CompleteSpace R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] in
lemma weierstrassDivision_bounds_r_gen (g : PowerSeries.Restricted R c) (s : ℕ)
    (hg : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted R c)
    (q : PowerSeries.Restricted R c) (r : Polynomial R) (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted c r)) :
    ‖(Polynomial.toRestricted c r)‖ ≤ ‖f‖ := by
  by_contra hcon
  exact contra_gen g s hg f q r hr hf (lt_max_iff.mpr (Or.inr (not_le.mp hcon)))

omit [CompleteSpace R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] in
/-- The quotient in a Weierstrass division at parameter `c` is unique. -/
lemma weierstrassDivision_q_unique_gen (g : PowerSeries.Restricted R c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted R c)
    {q₁ q₂ : PowerSeries.Restricted R c} {r₁ r₂ : Polynomial R}
    (hr₁ : Polynomial.degree r₁ < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted c r₁)
    (hr₂ : Polynomial.degree r₂ < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted c r₂) :
    q₁ = q₂ := by
  have h0 : g * (q₁ - q₂) + Polynomial.toRestricted c (r₁ - r₂) = 0 := by
    calc g * (q₁ - q₂) + Polynomial.toRestricted c (r₁ - r₂)
        = g * q₁ - g * q₂ +
            (Polynomial.toRestricted c r₁ - Polynomial.toRestricted c r₂) := by
          rw [mul_sub, Polynomial.toRestricted_sub]
      _ = (g * q₁ + Polynomial.toRestricted c r₁) -
            (g * q₂ + Polynomial.toRestricted c r₂) := by ring
      _ = 0 := by rw [← hf₁, ← hf₂, sub_self]
  have h_bd := weierstrassDivision_bounds_q_gen g s gd 0 (q₁ - q₂) (r₁ - r₂)
    (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr₁ hr₂)) h0.symm
  simp only [norm_zero, mul_zero, norm_le_zero_iff] at h_bd
  exact sub_eq_zero.mp h_bd

lemma weierstrassDivision_existance_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g : PowerSeries.Restricted R c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted R c)
    (h : ∃ a : R, ‖a‖ = ‖g‖⁻¹ ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (q : PowerSeries.Restricted R c) (r : Polynomial R),
      Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted c r) := by
  obtain ⟨u, hu⟩ := hα
  have h1 : ∃ a : R, ‖a‖ = ‖Restricted.rescaleEquiv u hu g‖⁻¹ ∧ IsUnit a := by
    rwa [Restricted.norm_rescaleEquiv u hu g]
  obtain ⟨q₁, r₁, hr₁, hf₁⟩ := weierstrassDivision_existance (Restricted.rescaleEquiv u hu g) s
    ((distinguished_rescaleEquiv u hu g s).mpr gd) (Restricted.rescaleEquiv u hu f) h1
    (hunit_transport u hu hunit)
  refine ⟨(Restricted.rescaleEquiv u hu).symm q₁,
    r₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X),
    degree_comp_C_mul_X_lt hr₁ _, ?_⟩
  have h2 := congrArg (Restricted.rescaleEquiv u hu).symm hf₁
  rwa [RingEquiv.symm_apply_apply, map_add, map_mul, RingEquiv.symm_apply_apply,
    Restricted.rescaleEquiv_symm_toRestricted] at h2

lemma weierstrassDivision_uniqueness_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g : PowerSeries.Restricted R c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted R c)
    (h : ∃ a : R, ‖a‖ = ‖g‖⁻¹ ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : PowerSeries.Restricted R c, ∃! r : Polynomial R,
      Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted c r) := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance_gen hα g s gd f h hunit
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf'.symm.trans hf₀)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact weierstrassDivision_q_unique_gen g s gd f hr' hf' hr₀ hf₀

/-- Weierstrass division for polynomials at parameter `c` (cf.
`weierstrassDivision_polynomial`; the hypothesis `hgs` is necessary for the same reason as at
`c = 1`). -/
lemma weierstrassDivision_polynomial_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g₀ : Polynomial R) (s : ℕ)
    (gd : distinguishedGen norm c (Polynomial.toRestricted c g₀).1 s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial R)
    (h : ∃ a : R, ‖a‖ = ‖Polynomial.toRestricted c g₀‖⁻¹ ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : Polynomial R, ∃! r : Polynomial R, Polynomial.degree r < s ∧
      Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ * Polynomial.toRestricted c q
        + Polynomial.toRestricted c r := by
  obtain ⟨u, hu⟩ := hα
  have gd1 : distinguished norm 1
      (Polynomial.toRestricted 1 (g₀.comp (Polynomial.C (u : R) * Polynomial.X))).1 s := by
    have h1 := (distinguished_rescaleEquiv u hu (Polynomial.toRestricted c g₀) s).mpr gd
    rwa [Restricted.rescaleEquiv_toRestricted] at h1
  have h1 : ∃ a : R, ‖a‖ =
      ‖Polynomial.toRestricted 1 (g₀.comp (Polynomial.C (u : R) * Polynomial.X))‖⁻¹ ∧
      IsUnit a := by
    rwa [← Restricted.rescaleEquiv_toRestricted u hu g₀, Restricted.norm_rescaleEquiv]
  obtain ⟨q₁, ⟨r₁, ⟨hr₁, heq₁⟩, -⟩, -⟩ := weierstrassDivision_polynomial
    (g₀.comp (Polynomial.C (u : R) * Polynomial.X)) s gd1
    (degree_comp_C_mul_X_le_of hgs _) (f₀.comp (Polynomial.C (u : R) * Polynomial.X)) h1
    (hunit_transport u hu hunit)
  have heqc : Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ *
      Polynomial.toRestricted c (q₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) +
      Polynomial.toRestricted c (r₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) := by
    have h2 := congrArg (Restricted.rescaleEquiv u hu).symm heq₁
    simpa only [map_add, map_mul, Restricted.rescaleEquiv_symm_toRestricted,
      comp_C_mul_X_cancel] using h2
  refine ⟨q₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X),
    ⟨r₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X),
      ⟨degree_comp_C_mul_X_lt hr₁ _, heqc⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf'.symm.trans heqc)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    have hq := weierstrassDivision_q_unique_gen (Polynomial.toRestricted c g₀) s gd
      (Polynomial.toRestricted c f₀) hr' hf' (degree_comp_C_mul_X_lt hr₁ _) heqc
    exact Polynomial.coe_inj.mp (congrArg Subtype.val hq)

omit [CompleteSpace R] [NormMulClass R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R] in
/-- A monic polynomial `ω` of degree `s` with `‖ω‖ = cˢ` is distinguished of degree `s` at
parameter `c` — the general-`c` normalisation of `distinguished_of_monic`: the top Gauss term
is `‖1‖ · cˢ`, so `‖ω‖ = cˢ` says the top term attains the norm. -/
lemma distinguished_of_monic_gen (ω : Polynomial R) (s : ℕ) (ωm : ω.Monic) (ωd : ω.degree = s)
    (ωn : ‖Polynomial.toRestricted c ω‖ = c ^ s) :
    distinguishedGen norm c (Polynomial.toRestricted c ω).1 s := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  have hnat : ω.natDegree = s := Polynomial.natDegree_eq_of_degree_eq_some ωd
  have hcs : ω.coeff s = 1 := by rw [← hnat]; exact ωm.coeff_natDegree
  have hcoe : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted c ω).1 = ω.coeff v :=
    fun v => Polynomial.coeff_coe ω v
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · rw [hcoe, hcs]
    exact isUnit_one
  · rw [← Restricted.norm_eq, ωn, hcoe, hcs, norm_one, one_mul]
  · rw [hcoe, hcoe, hcs, norm_one, one_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hnat.trans_lt ht), norm_zero, zero_mul]
    exact pow_pos hc0 s

/-- **Weierstrass preparation at `c = ‖unit‖`, existence** (cf.
`weierstrassPreparation_exists`): `g = e · ω` with `ω` monic of degree `s`, `‖ω‖ = cˢ`, and
`e` a unit of the restricted ring. -/
lemma weierstrassPreparation_exists_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g : PowerSeries.Restricted R c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (ω : Polynomial R) (e : PowerSeries.Restricted R c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * (Polynomial.toRestricted c ω) := by
  obtain ⟨u, hu⟩ := hα
  obtain ⟨ω₁, e₁, hm₁, hd₁, hn₁, he₁, hg₁⟩ :=
    weierstrassPreparation_exists (Restricted.rescaleEquiv u hu g) s
      ((distinguished_rescaleEquiv u hu g s).mpr gd) (hunit_transport u hu hunit)
  have hnat₁ : ω₁.natDegree = s := Polynomial.natDegree_eq_of_degree_eq_some hd₁
  have hcs₁ : ω₁.coeff s = 1 := by rw [← hnat₁]; exact hm₁.coeff_natDegree
  -- the pulled-back distinguished polynomial is `ω(x) = uˢ · ω₁(u⁻¹x)`, renormalised monic
  have hcoeffs : (Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X))).coeff s = 1 := by
    rw [Polynomial.coeff_C_mul, coeff_comp_C_mul_X, hcs₁, mul_one, ← mul_pow, Units.mul_inv,
      one_pow]
  have hdegle : (Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X))).degree ≤ (s : WithBot ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [Polynomial.coeff_C_mul, coeff_comp_C_mul_X,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hnat₁.trans_lt (by exact_mod_cast hm)),
      mul_zero, mul_zero]
  have hωdeg : (Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X))).degree = (s : WithBot ℕ) :=
    le_antisymm hdegle (Polynomial.le_degree_of_ne_zero (by rw [hcoeffs]; exact one_ne_zero))
  have hωmonic : (Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X))).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one s
      (Polynomial.natDegree_le_iff_degree_le.mpr hdegle) hcoeffs
  have hωcomp : (Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X))).comp
        (Polynomial.C (u : R) * Polynomial.X) = Polynomial.C ((u : R) ^ s) * ω₁ := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, comp_C_mul_X_cancel']
  have hCC : Polynomial.toRestricted c (Polynomial.C (((u⁻¹ : Rˣ) : R) ^ s)) *
      Polynomial.toRestricted c (Polynomial.C ((u : R) ^ s)) = 1 := by
    rw [← Polynomial.toRestricted_mul, ← Polynomial.C_mul, ← mul_pow, Units.inv_mul, one_pow,
      Polynomial.C_1]
    exact Subtype.ext Polynomial.coe_one
  refine ⟨Polynomial.C ((u : R) ^ s) *
      (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)),
    (Restricted.rescaleEquiv u hu).symm e₁ *
      Polynomial.toRestricted c (Polynomial.C (((u⁻¹ : Rˣ) : R) ^ s)),
    hωmonic, hωdeg, ?_, ?_, ?_⟩
  · -- `‖toRestricted c ω‖ = c ^ s`, via the isometry and `‖ω₁‖ = 1`
    rw [← Restricted.norm_rescaleEquiv u hu, Restricted.rescaleEquiv_toRestricted, hωcomp,
      Polynomial.toRestricted_mul, norm_mul, hn₁, mul_one,
      show Polynomial.toRestricted 1 (Polynomial.C ((u : R) ^ s))
        = PowerSeries.Restricted.C 1 ((u : R) ^ s) from Subtype.ext (Polynomial.coe_C _),
      PowerSeries.Restricted.norm_C, norm_pow, hu]
  · -- the unit
    exact (he₁.map (Restricted.rescaleEquiv u hu).symm).mul (IsUnit.of_mul_eq_one _ hCC)
  · -- the factorisation, pulled back along the isomorphism
    have h2 := congrArg (Restricted.rescaleEquiv u hu).symm hg₁
    rw [RingEquiv.symm_apply_apply, map_mul, Restricted.rescaleEquiv_symm_toRestricted] at h2
    calc g = (Restricted.rescaleEquiv u hu).symm e₁ *
          Polynomial.toRestricted c
            (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) := h2
      _ = (Restricted.rescaleEquiv u hu).symm e₁ *
            (Polynomial.toRestricted c (Polynomial.C (((u⁻¹ : Rˣ) : R) ^ s)) *
              Polynomial.toRestricted c (Polynomial.C ((u : R) ^ s))) *
            Polynomial.toRestricted c
              (ω₁.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) := by
          rw [hCC, mul_one]
      _ = _ := by rw [Polynomial.toRestricted_mul]; ring

lemma weierstrassPreparation_unique_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g : PowerSeries.Restricted R c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! ω : Polynomial R, ∃! e : PowerSeries.Restricted R c, ω.Monic ∧ ω.degree = s ∧
      ‖(Polynomial.toRestricted c ω)‖ = c ^ s ∧ IsUnit e ∧
      g = e * (Polynomial.toRestricted c ω) := by
  obtain ⟨ω, e, ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩ := weierstrassPreparation_exists_gen hα g s gd hunit
  have hcs : (0 : ℝ) < c ^ s := pow_pos (StrongPos_pos (fun _ : Unit ↦ c) ()) s
  refine ⟨ω, ⟨e, ⟨ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, -, hge'⟩
    have hsub : (e' - e) * Polynomial.toRestricted c ω = 0 := by
      rw [sub_mul, ← hge', ← hg1, sub_self]
    have hn0 : ‖e' - e‖ * ‖Polynomial.toRestricted c ω‖ = 0 := by
      rw [← norm_mul, hsub, norm_zero]
    rw [ωn] at hn0
    rcases mul_eq_zero.mp hn0 with h' | h'
    · exact sub_eq_zero.mp (norm_eq_zero.mp h')
    · exact absurd h' hcs.ne'
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, ⟨ue', hue'⟩, hg1'⟩, -⟩
    have rd : (ω' - ω).degree < (s : WithBot ℕ) := by
      simpa [ω'd] using Polynomial.degree_sub_lt (ω'd.trans ωd.symm) ω'm.ne_zero
        (by rw [ω'm.leadingCoeff, ωm.leadingCoeff])
    have h0 : (0 : PowerSeries.Restricted R c) =
        g * ((↑ue⁻¹ : PowerSeries.Restricted R c) - ↑ue'⁻¹) +
          Polynomial.toRestricted c (ω' - ω) := by
      rw [mul_sub, Polynomial.toRestricted_sub]
      have h1 : g * (↑ue⁻¹ : PowerSeries.Restricted R c) = Polynomial.toRestricted c ω := by
        rw [hg1, ← hue, mul_comm (↑ue : PowerSeries.Restricted R c) _, mul_assoc, ue.mul_inv,
          mul_one]
      have h2 : g * (↑ue'⁻¹ : PowerSeries.Restricted R c) = Polynomial.toRestricted c ω' := by
        rw [hg1', ← hue', mul_comm (↑ue' : PowerSeries.Restricted R c) _, mul_assoc,
          ue'.mul_inv, mul_one]
      grind
    rw [← sub_eq_zero]
    exact Polynomial.coe_inj.mp (congrArg Subtype.val (norm_le_zero_iff
      (a := Polynomial.toRestricted c (ω' - ω)).mp (by simpa [norm_zero] using
      (weierstrassDivision_bounds_r_gen g s gd 0 _ _ rd h0))))

/-- **Weierstrass preparation for polynomials at `c = ‖unit‖`** (cf.
`weierstrassPreparation_polynomial`): the unit `e` is itself a polynomial.  As at `c = 1`,
`IsUnit (Polynomial.toRestricted c e)` is unit-ness in the restricted ring, not in `R[X]`. -/
lemma weierstrassPreparation_polynomial_gen (hα : ∃ u : Rˣ, ‖(u : R)‖ = c)
    (g₀ : Polynomial R) (s : ℕ)
    (gd : distinguishedGen norm c (Polynomial.toRestricted c g₀).1 s)
    (hunit : ∀ f : PowerSeries.Restricted R c, f ≠ 0 →
      ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! ω : Polynomial R, ∃! e : Polynomial R, ω.Monic ∧ ω.degree = s ∧
      ‖(Polynomial.toRestricted c ω)‖ = c ^ s ∧ IsUnit (Polynomial.toRestricted c e) ∧
      Polynomial.toRestricted c g₀ =
        Polynomial.toRestricted c e * (Polynomial.toRestricted c ω) := by
  obtain ⟨u, hu⟩ := hα
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg⟩, he_uniq⟩, hω_uniq⟩ :=
    weierstrassPreparation_unique_gen ⟨u, hu⟩ (Polynomial.toRestricted c g₀) s gd hunit
  have h0 : (0 : Polynomial R).degree < (s : WithBot ℕ) := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe s
  -- the only new content over uniqueness: the unit `e` is a polynomial, being the quotient of
  -- the Weierstrass division of `g₀` by the distinguished polynomial `ω`
  obtain ⟨e₀, ⟨r₀, ⟨hr₀, hf₀⟩, -⟩, -⟩ := weierstrassDivision_polynomial_gen ⟨u, hu⟩ ω s
    (distinguished_of_monic_gen ω s ωm ωd ωn) ωd.le g₀
    ⟨((u⁻¹ : Rˣ) : R) ^ s, by rw [norm_pow, norm_units_inv u hu, ωn, inv_pow],
      (u⁻¹ ^ s).isUnit⟩ hunit
  have he₀ : e = Polynomial.toRestricted c e₀ :=
    weierstrassDivision_q_unique_gen (Polynomial.toRestricted c ω) s
      (distinguished_of_monic_gen ω s ωm ωd ωn) (Polynomial.toRestricted c g₀) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg, mul_comm]) hr₀ hf₀
  have hg₀ : Polynomial.toRestricted c g₀ =
      Polynomial.toRestricted c e₀ * Polynomial.toRestricted c ω := he₀ ▸ hg
  refine ⟨ω, ⟨e₀, ⟨ωm, ωd, ωn, he₀ ▸ he, hg₀⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, hu', hg'⟩
    exact Polynomial.coe_inj.mp (congrArg Subtype.val
      ((he_uniq _ ⟨ωm, ωd, ωn, hu', hg'⟩).trans he₀))
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, -⟩
    refine hω_uniq ω' ⟨Polynomial.toRestricted c e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, ?_⟩
    rintro e'' ⟨-, -, -, -, hg''⟩
    exact weierstrassDivision_q_unique_gen (Polynomial.toRestricted c ω') s
      (distinguished_of_monic_gen ω' s ω'm ω'd ω'n) (Polynomial.toRestricted c g₀) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg'', mul_comm]) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg', mul_comm])

end GeneralParameter

/-! ## §4  Fields: discharging the scaling hypotheses, and base change

Over a field, once `c` is the norm of a unit the `h`/`hunit` hypotheses become theorems: the
Gauss norm of a nonzero restricted series is attained at some coefficient, so
`‖f‖ = ‖aₖ‖ cᵏ = ‖aₖ uᵏ‖` is a realised norm, and fields invert.

For rung 2 we also need coefficientwise base change of restricted series along an isometric
embedding `K ↪ L` (underlying map `PowerSeries.map (algebraMap K L)`), matching Gauss norms
and `distinguished`.

**Generality note (why a field appears here, and only here).**  §2–§3 keep the `c = 1`
architecture — an abstract normed commutative ring `R` with the `hunit` scaling hypothesis —
so the intended instantiation `R = Restricted S` over a field `S` (Tate algebras, giving
multivariate preparation via `RestrictedIso`) still goes through at rung 1: `hunit` is
provable for such `R`, and its units have norms exactly `|Sˣ|` (dominant constant
coefficient), so `hα` holds for every `c` in the value group of the bottom field `S`.  For
`c` only in the *divisible closure*, however, no extension of the ring `R` itself helps: the
`n`-th root of the radius must come from a finite extension `S' = S(α)` of the bottom *field*
of coefficients, with `R' = Restricted S'` (that is, `R ⊗_S S'`), and the descent runs along
an `S`-basis of `S'` — the component bounds, the norm-equivalence input, and the
spectral-norm existence are all theorems about the bottom field.  The statements below are
the **one-variable instance** (`R = K` itself the bottom field), which is exactly what
`PhD/Main/Test/test.lean` consumes.  The base-change and descent arguments are
variable-count-agnostic, so rung 2 should eventually be restated for `MvRestricted` over a
complete field bottom (radius tuple, distinguished in one chosen variable); the
univariate-over-`Restricted S` case then follows via `RestrictedIso` exactly as at `c = 1`,
and the one-variable statements below become its `σ = Unit` case. -/


-- not convinced this should be the divisble value group
-- may want it to be like c * n = ‖x‖
-- e.g. we  can multiply out denominators of c

/-- `c` lies in the divisible closure of the value group: some positive power of `c` is a
realised norm.  This is the canonical home of the definition; the Newton-polygon theory
(`PhD/Main/Test/test.lean`) imports it from here. -/
def MemDivisibleValueGroup (K : Type*) [Norm K] (c : ℝ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ ∃ x : K, ‖x‖ = c ^ n

section FieldParameter

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {c : ℝ} [StrongPos (fun _ : Unit ↦ c)]

-- as in §1, the Gauss norm on `Restricted K c` is multiplicative (`K` is a field)
local instance : NormMulClass (PowerSeries.Restricted K c) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ c)

omit [CompleteSpace K] in
/-- Over a field, the scaling hypothesis `hunit` of the division/preparation theorems is
automatic once `c` is the norm of a unit. -/
lemma exists_norm_inv_unit_gen (hα : ∃ u : Kˣ, ‖(u : K)‖ = c)
    (f : PowerSeries.Restricted K c) (hf : f ≠ 0) :
    ∃ a : K, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a := by
  obtain ⟨u, hu⟩ := hα
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  obtain ⟨k, hk⟩ := Restricted.gaussNorm_achieved' c hc0.le f
  have hnorm : ‖f‖ = ‖PowerSeries.coeff k f.1‖ * c ^ k := by rw [hk]; rfl
  have hcoeff : PowerSeries.coeff k f.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hnorm
    exact (norm_pos_iff.mpr hf).ne' hnorm
  have hx : PowerSeries.coeff k f.1 * (u : K) ^ k ≠ 0 :=
    mul_ne_zero hcoeff (pow_ne_zero _ u.ne_zero)
  refine ⟨(PowerSeries.coeff k f.1 * (u : K) ^ k)⁻¹, ?_,
    isUnit_iff_ne_zero.mpr (inv_ne_zero hx)⟩
  rw [norm_inv, norm_mul, norm_pow, hu, ← hnorm]

section BaseChange

variable (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [Algebra K L]

omit [IsUltrametricDist K] [CompleteSpace K] [StrongPos (fun _ : Unit ↦ c)]
  [IsUltrametricDist L] [CompleteSpace L] in
/-- Coefficientwise isometric base change preserves restrictedness: the Gauss terms are
literally equal. -/
private lemma isRestricted_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : PowerSeries K} (hf : PowerSeries.IsRestricted c f) :
    PowerSeries.IsRestricted c (PowerSeries.map (algebraMap K L) f) := by
  rw [PowerSeries.isRestricted_iff] at hf ⊢
  refine hf.congr fun k => ?_
  rw [PowerSeries.coeff_map, hiso]

/-- **Base change of restricted series** along an isometric embedding `K ↪ L`
(coefficientwise `algebraMap`; underlying map `PowerSeries.map (algebraMap K L)`). -/
noncomputable def Restricted.mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    PowerSeries.Restricted K c →+* PowerSeries.Restricted L c :=
  RingHom.codRestrict
    ((PowerSeries.map (algebraMap K L)).comp (PowerSeries.isSubring (R := K) c).subtype)
    (PowerSeries.isSubring (R := L) c)
    (fun f => isRestricted_mapAlgebra L hiso f.2)

omit [CompleteSpace K] [StrongPos (fun _ : Unit ↦ c)] [CompleteSpace L] in
lemma Restricted.mapAlgebra_coe (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : PowerSeries.Restricted K c) :
    (Restricted.mapAlgebra L hiso f).1 = PowerSeries.map (algebraMap K L) f.1 := rfl

omit [CompleteSpace K] [CompleteSpace L] in
/-- Base change is a Gauss-norm isometry (termwise, by `hiso`). -/
lemma Restricted.norm_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : PowerSeries.Restricted K c) :
    ‖Restricted.mapAlgebra L hiso f‖ = ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, Restricted.mapAlgebra_coe,
    PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  exact iSup_congr fun k => by rw [PowerSeries.coeff_map, hiso]

omit [CompleteSpace K] [StrongPos (fun _ : Unit ↦ c)] [CompleteSpace L] in
lemma Restricted.mapAlgebra_toRestricted (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (ω : Polynomial K) :
    Restricted.mapAlgebra L hiso (Polynomial.toRestricted c ω)
      = Polynomial.toRestricted c (ω.map (algebraMap K L)) := by
  refine Subtype.ext ?_
  show PowerSeries.map (algebraMap K L) (ω : PowerSeries K)
      = ((ω.map (algebraMap K L) : Polynomial L) : PowerSeries L)
  ext k
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]

omit [CompleteSpace K] [StrongPos (fun _ : Unit ↦ c)] [CompleteSpace L] in
/-- `distinguished` transfers along base change (over fields, unit coefficients are nonzero
coefficients, and `hiso` preserves every Gauss term). -/
lemma distinguished_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : PowerSeries.Restricted K c) (s : ℕ) :
    distinguishedGen norm c (Restricted.mapAlgebra L hiso f).1 s ↔
      distinguishedGen norm c f.1 s := by
  rw [Restricted.mapAlgebra_coe]
  have hcoeff : ∀ k, ‖PowerSeries.coeff k (PowerSeries.map (algebraMap K L) f.1)‖
      = ‖PowerSeries.coeff k f.1‖ := fun k => by rw [PowerSeries.coeff_map, hiso]
  have hgauss : PowerSeries.gaussNorm norm c (PowerSeries.map (algebraMap K L) f.1)
      = PowerSeries.gaussNorm norm c f.1 := by
    rw [PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
    exact iSup_congr fun k => by rw [hcoeff]
  have hunit : ∀ k, IsUnit (PowerSeries.coeff k (PowerSeries.map (algebraMap K L) f.1))
      ↔ IsUnit (PowerSeries.coeff k f.1) := fun k => by
    rw [PowerSeries.coeff_map]
    constructor
    · intro h
      rw [isUnit_iff_ne_zero] at h ⊢
      intro h0
      exact h (by rw [h0, map_zero])
    · exact fun h => h.map (algebraMap K L)
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(hunit s).mp h1, by rw [← hgauss, h2, hcoeff],
      fun t ht => by have := h3 t ht; rwa [hcoeff, hcoeff] at this⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(hunit s).mpr h1, by rw [hgauss, h2, hcoeff],
      fun t ht => by rw [hcoeff, hcoeff]; exact h3 t ht⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- A `K`-linear functional applied coefficientwise pulls a product with a base-changed series
back to a product over `K`: termwise, `π (algebraMap(gₐ) · h_b) = gₐ · π (h_b)`. -/
private lemma lmap_mul (π : L →ₗ[K] K) (g : PowerSeries K) (h : PowerSeries L) :
    (PowerSeries.mk fun n => π (PowerSeries.coeff n
        (PowerSeries.map (algebraMap K L) g * h)))
      = g * PowerSeries.mk fun n => π (PowerSeries.coeff n h) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [CompleteSpace L] in
/-- **Descent by uniqueness (rung 2, core).**  A Weierstrass division over a finite isometric
extension `L`, of data defined over `K`, descends to `K`.

Proof (no Galois theory, no separability, no basis): pick a `K`-linear retraction `π` of the
embedding `K ↪ L` (a left inverse of `algebraMap`, which exists over a field and is bounded
because `L` is finite-dimensional over the complete field `K`).  Applied coefficientwise, `π`
carries `Restricted L c` to `Restricted K c` and satisfies `π(algebraMap(gₐ)·x) = gₐ·π(x)`,
so the retraction of the `L`-division of `f` by `g` is a `K`-division `f = g·q₀ + r₀`.  The
difference `(q − q₀, r − r₀)` is then an `L`-division of `0`, which the bounds
`weierstrassDivision_bounds_q_gen`/`_r_gen` force to vanish — this is where it matters that
those bounds need **no** unit of norm `c`. -/
lemma weierstrassDivision_descend [Module.Finite K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (g : PowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted K c)
    {q : PowerSeries.Restricted L c} {r : Polynomial L}
    (hr : Polynomial.degree r < s)
    (hf : Restricted.mapAlgebra L hiso f
      = Restricted.mapAlgebra L hiso g * q + Polynomial.toRestricted c r) :
    ∃ (q₀ : PowerSeries.Restricted K c) (r₀ : Polynomial K),
      Polynomial.degree r₀ < s ∧ f = g * q₀ + Polynomial.toRestricted c r₀ ∧
      Restricted.mapAlgebra L hiso q₀ = q ∧ r₀.map (algebraMap K L) = r := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  -- `L` is a normed `K`-space via the isometric embedding
  letI : NormedSpace K L :=
    ⟨fun a x => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  -- a `K`-linear retraction `π` of the embedding, bounded by finite-dimensionality
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hπ : ∀ a : K, π (algebraMap K L a) = a := fun a => LinearMap.congr_fun hπcomp a
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  -- the coefficientwise retraction of `q` is restricted over `K`
  have hq0res : PowerSeries.IsRestricted c
      (PowerSeries.mk fun n => π (PowerSeries.coeff n q.1)) := by
    rw [PowerSeries.isRestricted_iff]
    have h0 : Filter.Tendsto
        (fun n : ℕ => Cπ * (‖PowerSeries.coeff n q.1‖ * c ^ n)) Filter.cofinite (nhds 0) := by
      simpa using ((PowerSeries.isRestricted_iff c q.1).mp q.2).const_mul Cπ
    refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le n))
      (fun n => ?_) h0
    rw [PowerSeries.coeff_mk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hCπ _) (pow_pos hc0 n).le
  -- the coefficientwise retraction of `r`, as a polynomial over `K`
  have hr₀coeff : ∀ k, (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))).coeff k
      = π (r.coeff k) := by
    intro k
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' r.support k fun n => π (r.coeff n)]
    split_ifs with hk
    · rfl
    · rw [show r.coeff k = 0 from by simpa [Polynomial.mem_support_iff] using hk, map_zero]
  have hr₀deg : (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))).degree < s := by
    rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
    intro m hm
    rw [hr₀coeff, hr m hm, map_zero]
  -- the `L`-level equation at the level of raw power series
  have hf1 : PowerSeries.map (algebraMap K L) f.1
      = PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L) := by
    have h := congrArg Subtype.val hf
    rwa [show (Restricted.mapAlgebra L hiso g * q + Polynomial.toRestricted c r).1
        = (Restricted.mapAlgebra L hiso g).1 * q.1 + (r : PowerSeries L) from rfl,
      Restricted.mapAlgebra_coe, Restricted.mapAlgebra_coe] at h
  -- applying `π` coefficientwise gives the `K`-level division
  have hK : f = g * ⟨PowerSeries.mk fun n => π (PowerSeries.coeff n q.1), hq0res⟩ +
      Polynomial.toRestricted c (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))) := by
    refine Subtype.ext ?_
    show f.1 = g.1 * PowerSeries.mk (fun n => π (PowerSeries.coeff n q.1)) +
      ((∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) : Polynomial K) :
        PowerSeries K)
    have h2 : PowerSeries.mk (fun n => π (PowerSeries.coeff n
          (PowerSeries.map (algebraMap K L) f.1)))
        = PowerSeries.mk (fun n => π (PowerSeries.coeff n
            (PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L)))) :=
      congrArg (fun h : PowerSeries L => PowerSeries.mk fun n => π (PowerSeries.coeff n h)) hf1
    rwa [show (PowerSeries.mk fun n => π (PowerSeries.coeff n
          (PowerSeries.map (algebraMap K L) f.1))) = f.1 from by
        ext n; rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, hπ],
      show (PowerSeries.mk fun n => π (PowerSeries.coeff n
          (PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L))))
        = (PowerSeries.mk fun n => π (PowerSeries.coeff n
            (PowerSeries.map (algebraMap K L) g.1 * q.1)))
          + PowerSeries.mk fun n => π (PowerSeries.coeff n (r : PowerSeries L)) from by
        ext n; simp [map_add],
      lmap_mul,
      show (PowerSeries.mk fun n => π (PowerSeries.coeff n (r : PowerSeries L)))
        = ((∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) : Polynomial K) :
            PowerSeries K) from by
        ext n
        rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_coe,
          hr₀coeff]] at h2
  -- the `L`-side difference is a division of `0`, so it vanishes by the bounds
  have hzero : (0 : PowerSeries.Restricted L c) = Restricted.mapAlgebra L hiso g *
      (q - Restricted.mapAlgebra L hiso
        ⟨PowerSeries.mk fun n => π (PowerSeries.coeff n q.1), hq0res⟩) +
      Polynomial.toRestricted c (r - (∑ n ∈ r.support,
        Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L)) := by
    have hmapK := congrArg (Restricted.mapAlgebra L hiso) hK
    rw [map_add, map_mul, Restricted.mapAlgebra_toRestricted] at hmapK
    rw [mul_sub, Polynomial.toRestricted_sub]
    linear_combination hf - hmapK
  have hdegρ : (r - (∑ n ∈ r.support,
      Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L)).degree < s :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt hr (lt_of_le_of_lt Polynomial.degree_map_le hr₀deg))
  have hgd' : distinguishedGen norm c (Restricted.mapAlgebra L hiso g).1 s :=
    (distinguished_mapAlgebra L hiso g s).mpr gd
  have hq_eq : q - Restricted.mapAlgebra L hiso
      ⟨PowerSeries.mk fun n => π (PowerSeries.coeff n q.1), hq0res⟩ = 0 := by
    have hb := weierstrassDivision_bounds_q_gen (Restricted.mapAlgebra L hiso g) s hgd' 0
      _ _ hdegρ hzero
    simp only [norm_zero, mul_zero, norm_le_zero_iff] at hb
    exact hb
  have hr_eq : r - (∑ n ∈ r.support,
      Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L) = 0 := by
    have hb := weierstrassDivision_bounds_r_gen (Restricted.mapAlgebra L hiso g) s hgd' 0
      _ _ hdegρ hzero
    simp only [norm_zero, norm_le_zero_iff] at hb
    exact Polynomial.coe_inj.mp (congrArg Subtype.val hb)
  exact ⟨⟨PowerSeries.mk fun n => π (PowerSeries.coeff n q.1), hq0res⟩,
    ∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)), hr₀deg, hK,
    (sub_eq_zero.mp hq_eq).symm, (sub_eq_zero.mp hr_eq).symm⟩

omit [CompleteSpace L] in
/-- Unit-ness descends along isometric base change: retract the inverse coefficientwise. -/
private lemma isUnit_of_isUnit_mapAlgebra [Module.Finite K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) {q : PowerSeries.Restricted K c}
    (h : IsUnit (Restricted.mapAlgebra L hiso q)) : IsUnit q := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  letI : NormedSpace K L :=
    ⟨fun a x => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hπ : ∀ a : K, π (algebraMap K L a) = a := fun a => LinearMap.congr_fun hπcomp a
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  obtain ⟨v, hv⟩ := h
  have hEres : PowerSeries.IsRestricted c (PowerSeries.mk fun n =>
      π (PowerSeries.coeff n (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) :
        PowerSeries.Restricted L c)).1)) := by
    rw [PowerSeries.isRestricted_iff]
    have h0 : Filter.Tendsto (fun n : ℕ => Cπ * (‖PowerSeries.coeff n
        (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c)).1‖ * c ^ n))
        Filter.cofinite (nhds 0) := by
      simpa using ((PowerSeries.isRestricted_iff c _).mp
        ((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c).2).const_mul Cπ
    refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le n))
      (fun n => ?_) h0
    rw [PowerSeries.coeff_mk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hCπ _) (pow_pos hc0 n).le
  have hqv1 : PowerSeries.map (algebraMap K L) q.1 *
      (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c)).1 = 1 := by
    have hqv : Restricted.mapAlgebra L hiso q * ((v⁻¹ : (PowerSeries.Restricted L c)ˣ) :
        PowerSeries.Restricted L c) = 1 := by
      rw [← hv, Units.mul_inv]
    have h1 := congrArg Subtype.val hqv
    rwa [show (Restricted.mapAlgebra L hiso q * ((v⁻¹ : (PowerSeries.Restricted L c)ˣ) :
        PowerSeries.Restricted L c)).1 = (Restricted.mapAlgebra L hiso q).1 *
        (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c)).1 from rfl,
      Restricted.mapAlgebra_coe] at h1
  let Einv : PowerSeries.Restricted K c :=
    ⟨PowerSeries.mk fun n => π (PowerSeries.coeff n
      (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c)).1), hEres⟩
  have hone : q * Einv = 1 := by
    apply Subtype.ext
    show q.1 * PowerSeries.mk (fun n => π (PowerSeries.coeff n _)) = 1
    have h2 : PowerSeries.mk (fun n => π (PowerSeries.coeff n
          (PowerSeries.map (algebraMap K L) q.1 *
            (((v⁻¹ : (PowerSeries.Restricted L c)ˣ) : PowerSeries.Restricted L c)).1)))
        = PowerSeries.mk (fun n => π (PowerSeries.coeff n (1 : PowerSeries L))) :=
      congrArg (fun h : PowerSeries L =>
        PowerSeries.mk fun n => π (PowerSeries.coeff n h)) hqv1
    rwa [lmap_mul, show (PowerSeries.mk fun n =>
        π (PowerSeries.coeff n (1 : PowerSeries L))) = 1 from by
      ext n
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_one]
      split_ifs with hn0
      · rw [show (1 : L) = algebraMap K L 1 from (map_one _).symm, hπ]
      · exact map_zero π] at h2
  exact IsUnit.of_mul_eq_one _ hone

end BaseChange

/-! ## §5  Endpoints: division and preparation at any `c` in the divisible closure

The statements the Newton-polygon theory consumes.  No `h`/`hunit` hypotheses appear — over
`K` itself they may *fail* at an unrealised radius `c` (no element of `K` has norm `‖f‖⁻¹`),
and the proofs do not need them.  Given `‖x‖ = cⁿ`, the extension `E = K⟮α⟯` with `αⁿ = x` is
taken inside `AlgebraicClosure K`, normed by Mathlib's spectral norm
(`spectralNorm.nontriviallyNormedField`) — complete because it is finite-dimensional over the
complete `K`, isometric over `K` by `spectralNorm_extends`, and `‖α‖ = c` there.  So the
`_gen` results of §3 apply over `E` with `hunit` discharged by `exists_norm_inv_unit_gen`,
and descend along `weierstrassDivision_descend`.  For the *preparation*, the factor `ω_L`
over `E` is recovered over `K` by descending the division of `X^s` by `g` (whose `E`-quotient
is the unit `e_L⁻¹` and whose remainder is `X^s − ω_L`), and unit-ness of the descended
quotient comes from `isUnit_of_isUnit_mapAlgebra`; uniqueness and the polynomial refinements
are then `K`-level arguments on top of the unit-free bounds of §3. -/

open IntermediateField in
theorem weierstrassDivision_existance_divisible (hdiv : MemDivisibleValueGroup K c)
    (g : PowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted K c) :
    ∃ (q : PowerSeries.Restricted K c) (r : Polynomial K),
      Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted c r) := by
  obtain ⟨n, hn, x, hx⟩ := hdiv
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  -- the finite extension `E = K(α)`, `αⁿ = x`, with the spectral norm
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) x) (Nat.pos_of_ne_zero hn)
  haveI hfin : FiniteDimensional K ↥K⟮α⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  haveI : Algebra.IsAlgebraic K ↥K⟮α⟯ := Algebra.IsAlgebraic.of_finite K _
  letI : NontriviallyNormedField ↥K⟮α⟯ := spectralNorm.nontriviallyNormedField K _
  haveI : IsUltrametricDist ↥K⟮α⟯ :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hiso : ∀ a : K, ‖algebraMap K ↥K⟮α⟯ a‖ = ‖a‖ := fun a => spectralNorm_extends a
  letI : NormedSpace K ↥K⟮α⟯ :=
    ⟨fun a y => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  haveI : CompleteSpace ↥K⟮α⟯ := FiniteDimensional.complete K _
  haveI : Filter.NeBot (𝓝[≠] (0 : ↥K⟮α⟯)) := NormedField.nhdsNE_neBot 0
  -- the root realises the radius as the norm of a unit of `E`
  have hgen : IntermediateField.AdjoinSimple.gen K α ^ n = algebraMap K ↥K⟮α⟯ x := by
    apply (algebraMap ↥K⟮α⟯ (AlgebraicClosure K)).injective
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, hα,
      ← IsScalarTower.algebraMap_apply]
  have hgnorm : ‖IntermediateField.AdjoinSimple.gen K α‖ = c := by
    refine (pow_left_inj₀ (norm_nonneg _) hc0.le hn).mp ?_
    rw [← norm_pow, hgen, hiso, hx]
  have hgne : IntermediateField.AdjoinSimple.gen K α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgnorm
    exact hc0.ne hgnorm
  have hunitE : ∃ u : (↥K⟮α⟯)ˣ, ‖(u : ↥K⟮α⟯)‖ = c := ⟨Units.mk0 _ hgne, hgnorm⟩
  -- divide over `E` and descend
  have hgz : g ≠ 0 := fun h0 => gd.ne_zero (by rw [h0]; rfl)
  have hmapgz : Restricted.mapAlgebra ↥K⟮α⟯ hiso g ≠ 0 := by
    intro h0
    have hn0 := Restricted.norm_mapAlgebra ↥K⟮α⟯ hiso g
    rw [h0, norm_zero] at hn0
    exact (norm_pos_iff.mpr hgz).ne' hn0.symm
  obtain ⟨q₁, r₁, hr₁, hf₁⟩ := weierstrassDivision_existance_gen hunitE
    (Restricted.mapAlgebra ↥K⟮α⟯ hiso g) s
    ((distinguished_mapAlgebra ↥K⟮α⟯ hiso g s).mpr gd)
    (Restricted.mapAlgebra ↥K⟮α⟯ hiso f)
    (exists_norm_inv_unit_gen hunitE _ hmapgz)
    (fun f' hf' => exists_norm_inv_unit_gen hunitE f' hf')
  obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ :=
    weierstrassDivision_descend ↥K⟮α⟯ hiso g s gd f hr₁ hf₁
  exact ⟨q₀, r₀, hr₀, heq⟩

theorem weierstrassDivision_uniqueness_divisible (hdiv : MemDivisibleValueGroup K c)
    (g : PowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) (f : PowerSeries.Restricted K c) :
    ∃! q : PowerSeries.Restricted K c, ∃! r : Polynomial K,
      Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted c r) := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance_divisible hdiv g s gd f
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf'.symm.trans hf₀)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact weierstrassDivision_q_unique_gen g s gd f hr' hf' hr₀ hf₀

theorem weierstrassDivision_polynomial_divisible (hdiv : MemDivisibleValueGroup K c)
    (g₀ : Polynomial K) (s : ℕ)
    (gd : distinguishedGen norm c (Polynomial.toRestricted c g₀).1 s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial K) :
    ∃! q : Polynomial K, ∃! r : Polynomial K, Polynomial.degree r < s ∧
      Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ * Polynomial.toRestricted c q
        + Polynomial.toRestricted c r := by
  -- `g₀` has degree exactly `s` with nonvanishing top coefficient, so rescaling makes it monic
  -- and ordinary polynomial division provides a polynomial solution (cf.
  -- `weierstrassDivision_polynomial`)
  have hgu : IsUnit (g₀.coeff s) := by
    have h1 : IsUnit (PowerSeries.coeff s (g₀ : PowerSeries K)) := gd.unit
    rwa [Polynomial.coeff_coe] at h1
  obtain ⟨u, hu⟩ := hgu
  have hdeg : g₀.degree = s :=
    le_antisymm hgs (Polynomial.le_degree_of_ne_zero (hu ▸ u.ne_zero))
  have hlead : g₀.leadingCoeff = g₀.coeff s :=
    congrArg g₀.coeff (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  have hmonic : (Polynomial.C (↑u⁻¹ : K) * g₀).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, ← hu, Units.inv_mul])
  have hdeg₁ : (Polynomial.C (↑u⁻¹ : K) * g₀).degree = s := by
    refine le_antisymm ?_ (Polynomial.le_degree_of_ne_zero ?_)
    · calc (Polynomial.C (↑u⁻¹ : K) * g₀).degree
          ≤ (Polynomial.C (↑u⁻¹ : K)).degree + g₀.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (s : WithBot ℕ) := add_le_add Polynomial.degree_C_le hdeg.le
        _ = s := zero_add _
    · rw [Polynomial.coeff_C_mul, ← hu, Units.inv_mul]
      exact one_ne_zero
  have hpoly : f₀ = g₀ * (Polynomial.C (↑u⁻¹ : K) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : K) * g₀))) +
      f₀ %ₘ (Polynomial.C (↑u⁻¹ : K) * g₀) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div f₀ (Polynomial.C (↑u⁻¹ : K) * g₀)]
    ring
  have hr₁ : (f₀ %ₘ (Polynomial.C (↑u⁻¹ : K) * g₀)).degree < s := by
    have h2 := Polynomial.degree_modByMonic_lt f₀ hmonic
    rwa [hdeg₁] at h2
  have hf₁ : Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ *
      Polynomial.toRestricted c (Polynomial.C (↑u⁻¹ : K) *
        (f₀ /ₘ (Polynomial.C (↑u⁻¹ : K) * g₀))) +
      Polynomial.toRestricted c (f₀ %ₘ (Polynomial.C (↑u⁻¹ : K) * g₀)) := by
    rw [← Polynomial.toRestricted_mul, ← Polynomial.toRestricted_add]
    exact congrArg _ hpoly
  obtain ⟨Q, -, hQ⟩ := weierstrassDivision_uniqueness_divisible hdiv
    (Polynomial.toRestricted c g₀) s gd (Polynomial.toRestricted c f₀)
  have key : ∀ (q' : PowerSeries.Restricted K c) (r' : Polynomial K),
      Polynomial.degree r' < s → Polynomial.toRestricted c f₀ =
        Polynomial.toRestricted c g₀ * q' + Polynomial.toRestricted c r' → q' = Q := by
    intro q' r' hr' hf'
    refine hQ q' ⟨r', ⟨hr', hf'⟩, ?_⟩
    rintro r'' ⟨-, hf''⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf''.symm.trans hf')))
  refine ⟨Polynomial.C (↑u⁻¹ : K) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : K) * g₀)),
    ⟨f₀ %ₘ (Polynomial.C (↑u⁻¹ : K) * g₀), ⟨hr₁, hf₁⟩, ?_⟩, ?_⟩
  · rintro r'' ⟨-, hf''⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf''.symm.trans hf₁)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.coe_inj.mp (congrArg Subtype.val
      ((key _ _ hr' hf').trans (key _ _ hr₁ hf₁).symm))

open IntermediateField in
theorem weierstrassPreparation_exists_divisible (hdiv : MemDivisibleValueGroup K c)
    (g : PowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) :
    ∃ (ω : Polynomial K) (e : PowerSeries.Restricted K c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * (Polynomial.toRestricted c ω) := by
  obtain ⟨n, hn, x, hx⟩ := hdiv
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  -- the finite extension `E = K(α)`, `αⁿ = x`, with the spectral norm
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) x) (Nat.pos_of_ne_zero hn)
  haveI hfin : FiniteDimensional K ↥K⟮α⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  haveI : Algebra.IsAlgebraic K ↥K⟮α⟯ := Algebra.IsAlgebraic.of_finite K _
  letI : NontriviallyNormedField ↥K⟮α⟯ := spectralNorm.nontriviallyNormedField K _
  haveI : IsUltrametricDist ↥K⟮α⟯ :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hiso : ∀ a : K, ‖algebraMap K ↥K⟮α⟯ a‖ = ‖a‖ := fun a => spectralNorm_extends a
  letI : NormedSpace K ↥K⟮α⟯ :=
    ⟨fun a y => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  haveI : CompleteSpace ↥K⟮α⟯ := FiniteDimensional.complete K _
  haveI : Filter.NeBot (𝓝[≠] (0 : ↥K⟮α⟯)) := NormedField.nhdsNE_neBot 0
  -- the root realises the radius as the norm of a unit of `E`
  have hgen : IntermediateField.AdjoinSimple.gen K α ^ n = algebraMap K ↥K⟮α⟯ x := by
    apply (algebraMap ↥K⟮α⟯ (AlgebraicClosure K)).injective
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, hα,
      ← IsScalarTower.algebraMap_apply]
  have hgnorm : ‖IntermediateField.AdjoinSimple.gen K α‖ = c := by
    refine (pow_left_inj₀ (norm_nonneg _) hc0.le hn).mp ?_
    rw [← norm_pow, hgen, hiso, hx]
  have hgne : IntermediateField.AdjoinSimple.gen K α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgnorm
    exact hc0.ne hgnorm
  have hunitE : ∃ u : (↥K⟮α⟯)ˣ, ‖(u : ↥K⟮α⟯)‖ = c := ⟨Units.mk0 _ hgne, hgnorm⟩
  -- Weierstrass preparation over `E`
  obtain ⟨ωL, eL, hmL, hdL, hnL, ⟨ue, hue⟩, hgL⟩ := weierstrassPreparation_exists_gen hunitE
    (Restricted.mapAlgebra ↥K⟮α⟯ hiso g) s
    ((distinguished_mapAlgebra ↥K⟮α⟯ hiso g s).mpr gd)
    (fun f' hf' => exists_norm_inv_unit_gen hunitE f' hf')
  -- over `E`, dividing `X^s` by `mapAlg g` has quotient `ue⁻¹` and remainder `X^s − ωL`, so
  -- descending that division recovers `ωL` (and the unit) over `K`
  have hrdeg : ((Polynomial.X : Polynomial ↥K⟮α⟯) ^ s - ωL).degree < s := by
    have hdd : ((Polynomial.X : Polynomial ↥K⟮α⟯) ^ s).degree = ωL.degree := by
      rw [Polynomial.degree_X_pow, hdL]
    have hlc : ((Polynomial.X : Polynomial ↥K⟮α⟯) ^ s).leadingCoeff = ωL.leadingCoeff := by
      rw [(Polynomial.monic_X_pow (n := s)).leadingCoeff, hmL.leadingCoeff]
    have h := Polynomial.degree_sub_lt hdd
      (pow_ne_zero s (Polynomial.X_ne_zero (R := ↥K⟮α⟯))) hlc
    rwa [Polynomial.degree_X_pow] at h
  have hdivE : Restricted.mapAlgebra ↥K⟮α⟯ hiso
      (Polynomial.toRestricted c ((Polynomial.X : Polynomial K) ^ s))
      = Restricted.mapAlgebra ↥K⟮α⟯ hiso g *
          ((ue⁻¹ : (PowerSeries.Restricted ↥K⟮α⟯ c)ˣ) : PowerSeries.Restricted ↥K⟮α⟯ c)
        + Polynomial.toRestricted c ((Polynomial.X : Polynomial ↥K⟮α⟯) ^ s - ωL) := by
    have h1 : Restricted.mapAlgebra ↥K⟮α⟯ hiso g *
        ((ue⁻¹ : (PowerSeries.Restricted ↥K⟮α⟯ c)ˣ) : PowerSeries.Restricted ↥K⟮α⟯ c)
        = Polynomial.toRestricted c ωL := by
      rw [hgL, ← hue, mul_comm (↑ue : PowerSeries.Restricted ↥K⟮α⟯ c) _, mul_assoc,
        ue.mul_inv, mul_one]
    rw [Restricted.mapAlgebra_toRestricted, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.toRestricted_sub, h1]
    ring
  obtain ⟨q₀, r₀, hr₀, heq, hq₀map, hr₀map⟩ :=
    weierstrassDivision_descend ↥K⟮α⟯ hiso g s gd
      (Polynomial.toRestricted c ((Polynomial.X : Polynomial K) ^ s)) hrdeg hdivE
  -- the descended factor `ω = X^s − r₀` and unit `q₀⁻¹`
  have hωmap : ((Polynomial.X : Polynomial K) ^ s - r₀).map (algebraMap K ↥K⟮α⟯) = ωL := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hr₀map]
    ring
  have hωmonic : ((Polynomial.X : Polynomial K) ^ s - r₀).Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one s
      (Polynomial.natDegree_le_iff_degree_le.mpr
        (le_trans (Polynomial.degree_sub_le _ _)
          (max_le (le_of_eq (Polynomial.degree_X_pow s)) hr₀.le))) ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt hr₀, sub_zero]
  have hωdeg : ((Polynomial.X : Polynomial K) ^ s - r₀).degree = s := by
    refine le_antisymm (le_trans (Polynomial.degree_sub_le _ _)
      (max_le (le_of_eq (Polynomial.degree_X_pow s)) hr₀.le))
      (Polynomial.le_degree_of_ne_zero ?_)
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt hr₀, sub_zero]
    exact one_ne_zero
  have hωnorm : ‖Polynomial.toRestricted c
      ((Polynomial.X : Polynomial K) ^ s - r₀)‖ = c ^ s := by
    rw [← Restricted.norm_mapAlgebra ↥K⟮α⟯ hiso, Restricted.mapAlgebra_toRestricted, hωmap,
      hnL]
  have hq₀unit : IsUnit q₀ := isUnit_of_isUnit_mapAlgebra ↥K⟮α⟯ hiso
    (by rw [hq₀map]; exact (ue⁻¹).isUnit)
  obtain ⟨uq, huq⟩ := hq₀unit
  refine ⟨(Polynomial.X : Polynomial K) ^ s - r₀,
    ((uq⁻¹ : (PowerSeries.Restricted K c)ˣ) : PowerSeries.Restricted K c),
    hωmonic, hωdeg, hωnorm, (uq⁻¹).isUnit, ?_⟩
  have hfact : Polynomial.toRestricted c ((Polynomial.X : Polynomial K) ^ s - r₀)
      = g * q₀ := by
    rw [Polynomial.toRestricted_sub, heq]
    ring
  rw [hfact, ← huq, mul_comm g, ← mul_assoc, uq.inv_mul, one_mul]

theorem weierstrassPreparation_unique_divisible (hdiv : MemDivisibleValueGroup K c)
    (g : PowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedGen norm c g.1 s) :
    ∃! ω : Polynomial K, ∃! e : PowerSeries.Restricted K c, ω.Monic ∧ ω.degree = s ∧
      ‖(Polynomial.toRestricted c ω)‖ = c ^ s ∧ IsUnit e ∧
      g = e * (Polynomial.toRestricted c ω) := by
  obtain ⟨ω, e, ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩ :=
    weierstrassPreparation_exists_divisible hdiv g s gd
  have hcs : (0 : ℝ) < c ^ s := pow_pos (StrongPos_pos (fun _ : Unit ↦ c) ()) s
  refine ⟨ω, ⟨e, ⟨ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, -, hge'⟩
    have hsub : (e' - e) * Polynomial.toRestricted c ω = 0 := by
      rw [sub_mul, ← hge', ← hg1, sub_self]
    have hn0 : ‖e' - e‖ * ‖Polynomial.toRestricted c ω‖ = 0 := by
      rw [← norm_mul, hsub, norm_zero]
    rw [ωn] at hn0
    rcases mul_eq_zero.mp hn0 with h' | h'
    · exact sub_eq_zero.mp (norm_eq_zero.mp h')
    · exact absurd h' hcs.ne'
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, ⟨ue', hue'⟩, hg1'⟩, -⟩
    have rd : (ω' - ω).degree < (s : WithBot ℕ) := by
      simpa [ω'd] using Polynomial.degree_sub_lt (ω'd.trans ωd.symm) ω'm.ne_zero
        (by rw [ω'm.leadingCoeff, ωm.leadingCoeff])
    have h0 : (0 : PowerSeries.Restricted K c) =
        g * ((↑ue⁻¹ : PowerSeries.Restricted K c) - ↑ue'⁻¹) +
          Polynomial.toRestricted c (ω' - ω) := by
      rw [mul_sub, Polynomial.toRestricted_sub]
      have h1 : g * (↑ue⁻¹ : PowerSeries.Restricted K c) = Polynomial.toRestricted c ω := by
        rw [hg1, ← hue, mul_comm (↑ue : PowerSeries.Restricted K c) _, mul_assoc, ue.mul_inv,
          mul_one]
      have h2 : g * (↑ue'⁻¹ : PowerSeries.Restricted K c) = Polynomial.toRestricted c ω' := by
        rw [hg1', ← hue', mul_comm (↑ue' : PowerSeries.Restricted K c) _, mul_assoc,
          ue'.mul_inv, mul_one]
      grind
    rw [← sub_eq_zero]
    exact Polynomial.coe_inj.mp (congrArg Subtype.val (norm_le_zero_iff
      (a := Polynomial.toRestricted c (ω' - ω)).mp (by simpa [norm_zero] using
      (weierstrassDivision_bounds_r_gen g s gd 0 _ _ rd h0))))

/-- **Weierstrass preparation for polynomials at any divisible-closure radius** — the
endpoint the Newton-polygon theory consumes. -/
theorem weierstrassPreparation_polynomial_divisible (hdiv : MemDivisibleValueGroup K c)
    (g₀ : Polynomial K) (s : ℕ)
    (gd : distinguishedGen norm c (Polynomial.toRestricted c g₀).1 s) :
    ∃! ω : Polynomial K, ∃! e : Polynomial K, ω.Monic ∧ ω.degree = s ∧
      ‖(Polynomial.toRestricted c ω)‖ = c ^ s ∧ IsUnit (Polynomial.toRestricted c e) ∧
      Polynomial.toRestricted c g₀ =
        Polynomial.toRestricted c e * (Polynomial.toRestricted c ω) := by
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg⟩, he_uniq⟩, hω_uniq⟩ :=
    weierstrassPreparation_unique_divisible hdiv (Polynomial.toRestricted c g₀) s gd
  have h0 : (0 : Polynomial K).degree < (s : WithBot ℕ) := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe s
  -- the only new content over uniqueness: the unit `e` is a polynomial, being the quotient of
  -- the Weierstrass division of `g₀` by the distinguished polynomial `ω`
  obtain ⟨e₀, ⟨r₀, ⟨hr₀, hf₀⟩, -⟩, -⟩ := weierstrassDivision_polynomial_divisible hdiv ω s
    (distinguished_of_monic_gen ω s ωm ωd ωn) ωd.le g₀
  have he₀ : e = Polynomial.toRestricted c e₀ :=
    weierstrassDivision_q_unique_gen (Polynomial.toRestricted c ω) s
      (distinguished_of_monic_gen ω s ωm ωd ωn) (Polynomial.toRestricted c g₀) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg, mul_comm]) hr₀ hf₀
  have hg₀ : Polynomial.toRestricted c g₀ =
      Polynomial.toRestricted c e₀ * Polynomial.toRestricted c ω := he₀ ▸ hg
  refine ⟨ω, ⟨e₀, ⟨ωm, ωd, ωn, he₀ ▸ he, hg₀⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, hu', hg'⟩
    exact Polynomial.coe_inj.mp (congrArg Subtype.val
      ((he_uniq _ ⟨ωm, ωd, ωn, hu', hg'⟩).trans he₀))
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, -⟩
    refine hω_uniq ω' ⟨Polynomial.toRestricted c e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, ?_⟩
    rintro e'' ⟨-, -, -, -, hg''⟩
    exact weierstrassDivision_q_unique_gen (Polynomial.toRestricted c ω') s
      (distinguished_of_monic_gen ω' s ω'm ω'd ω'n) (Polynomial.toRestricted c g₀) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg'', mul_comm]) h0
      (by rw [Polynomial.toRestricted_zero, add_zero, hg', mul_comm])

open IntermediateField in
/-- **Units of the restricted ring have strictly dominant constant coefficient** (at any
radius in the divisible closure): if `e` is a unit of `Restricted K c` then
`‖eₖ‖ · cᵏ < ‖e₀‖` for every `k ≥ 1`.  This transports the `c = 1` characterisation
`Restricted.isUnit_iff` along the rescaling over the spectral extension `E = K⟮α⟯`, and is
the last translation piece between the preparation theorems and the coefficient-norm form
consumed by the Newton-polygon theory. -/
theorem dominant_const_of_isUnit (hdiv : MemDivisibleValueGroup K c)
    {e : PowerSeries.Restricted K c} (he : IsUnit e) :
    ∀ k, 1 ≤ k → ‖PowerSeries.coeff k e.1‖ * c ^ k < ‖PowerSeries.coeff 0 e.1‖ := by
  obtain ⟨n, hn, x, hx⟩ := hdiv
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  -- the finite extension `E = K(α)`, `αⁿ = x`, with the spectral norm
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) x) (Nat.pos_of_ne_zero hn)
  haveI hfin : FiniteDimensional K ↥K⟮α⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  haveI : Algebra.IsAlgebraic K ↥K⟮α⟯ := Algebra.IsAlgebraic.of_finite K _
  letI : NontriviallyNormedField ↥K⟮α⟯ := spectralNorm.nontriviallyNormedField K _
  haveI : IsUltrametricDist ↥K⟮α⟯ :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hiso : ∀ a : K, ‖algebraMap K ↥K⟮α⟯ a‖ = ‖a‖ := fun a => spectralNorm_extends a
  letI : NormedSpace K ↥K⟮α⟯ :=
    ⟨fun a y => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  haveI : CompleteSpace ↥K⟮α⟯ := FiniteDimensional.complete K _
  haveI : Filter.NeBot (𝓝[≠] (0 : ↥K⟮α⟯)) := NormedField.nhdsNE_neBot 0
  have hgen : IntermediateField.AdjoinSimple.gen K α ^ n = algebraMap K ↥K⟮α⟯ x := by
    apply (algebraMap ↥K⟮α⟯ (AlgebraicClosure K)).injective
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, hα,
      ← IsScalarTower.algebraMap_apply]
  have hgnorm : ‖IntermediateField.AdjoinSimple.gen K α‖ = c := by
    refine (pow_left_inj₀ (norm_nonneg _) hc0.le hn).mp ?_
    rw [← norm_pow, hgen, hiso, hx]
  have hgne : IntermediateField.AdjoinSimple.gen K α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgnorm
    exact hc0.ne hgnorm
  -- instances for `Restricted E 1`
  haveI : StrongPos (fun _ : Unit ↦ (1 : ℝ)) := ⟨fun _ => one_pos⟩
  haveI : NormMulClass (PowerSeries.Restricted ↥K⟮α⟯ 1) :=
    MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ (1 : ℝ))
  haveI : Nontrivial (PowerSeries.Restricted ↥K⟮α⟯ 1) :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := PowerSeries ↥K⟮α⟯) (congrArg Subtype.val h)⟩⟩
  -- transport the unit to parameter `1` over `E`
  set F : PowerSeries.Restricted ↥K⟮α⟯ 1 :=
    Restricted.rescaleEquiv (Units.mk0 _ hgne) hgnorm
      (Restricted.mapAlgebra ↥K⟮α⟯ hiso e) with hF
  have hE : IsUnit F :=
    (he.map (Restricted.mapAlgebra ↥K⟮α⟯ hiso)).map
      (Restricted.rescaleEquiv (Units.mk0 _ hgne) hgnorm)
  -- the Gauss terms of `F` at parameter `1` are those of `e` at parameter `c`
  have hFcoeff : ∀ k : ℕ,
      ‖PowerSeries.coeff k F.1‖ = ‖PowerSeries.coeff k e.1‖ * c ^ k := by
    intro k
    rw [hF, Restricted.rescaleEquiv_coe, PowerSeries.coeff_rescale,
      Restricted.mapAlgebra_coe, PowerSeries.coeff_map, norm_mul, norm_pow, Units.val_mk0,
      hgnorm, hiso, mul_comm]
  -- the Gauss norm of `P` is positive and attained at some index `k₀`
  have hFpos : (0 : ℝ) < ‖F‖ := norm_pos_iff.mpr hE.ne_zero
  obtain ⟨k₀, hk₀⟩ :=
    Restricted.gaussNorm_achieved' 1 zero_le_one (F)
  rw [one_pow, mul_one] at hk₀
  have hk₀' : ‖PowerSeries.coeff k₀ (F).1‖
      = ‖F‖ := by rw [hk₀]; rfl
  have hd0 : PowerSeries.coeff k₀ (F).1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hk₀'
    exact hFpos.ne' hk₀'.symm
  -- normalise to norm `1` and apply the `c = 1` characterisation
  have hGunit : IsUnit (PowerSeries.Restricted.C 1
      (PowerSeries.coeff k₀ (F).1)⁻¹ *
        F) :=
    (PowerSeries.Restricted.C_isUnit 1
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hd0))).mul hE
  have hGnorm : ‖PowerSeries.Restricted.C 1
      (PowerSeries.coeff k₀ (F).1)⁻¹ *
        F‖ = 1 := by
    rw [norm_mul, PowerSeries.Restricted.norm_C, norm_inv, hk₀']
    exact inv_mul_cancel₀ hFpos.ne'
  obtain ⟨-, hlt1⟩ := (Restricted.isUnit_iff _ hGnorm).mp hGunit
  -- for every `k ≥ 1` the `k`-th Gauss term of `P` is strictly below the norm
  have hklt : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k (F).1‖
      < ‖F‖ := by
    intro k hk
    have h4 := PowerSeries.le_gaussNorm norm 1
      ((PowerSeries.Restricted.C 1
          (PowerSeries.coeff k₀ (F).1)⁻¹ *
            F) -
        PowerSeries.Restricted.C 1 (PowerSeries.coeff 0
          ((PowerSeries.Restricted.C 1
            (PowerSeries.coeff k₀ (F).1)⁻¹ *
              F)).1)).1
      (Restricted.hasGaussNorm 1 _) k
    rw [one_pow, mul_one, ← Restricted.norm_eq] at h4
    have h5 := lt_of_le_of_lt h4 hlt1
    rw [show ((PowerSeries.Restricted.C 1
          (PowerSeries.coeff k₀ (F).1)⁻¹ *
            F) -
        PowerSeries.Restricted.C 1 (PowerSeries.coeff 0
          ((PowerSeries.Restricted.C 1
            (PowerSeries.coeff k₀ (F).1)⁻¹ *
              F)).1)).1
        = PowerSeries.C (PowerSeries.coeff k₀ (F).1)⁻¹ *
            (F).1 -
          PowerSeries.C (PowerSeries.coeff 0
            ((PowerSeries.Restricted.C 1
              (PowerSeries.coeff k₀ (F).1)⁻¹ *
                F)).1) from rfl,
      map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C, if_neg (by omega), sub_zero,
      norm_mul, norm_inv, hk₀', ← div_eq_inv_mul] at h5
    exact (div_lt_one hFpos).mp h5
  -- the norm is therefore attained at the constant coefficient
  have hattain0 : ‖F‖
      = ‖PowerSeries.coeff 0 (F).1‖ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [← hk₀', h]
    · exact absurd (hk₀' ▸ hklt k₀ h) (lt_irrefl _)
  -- translate back to the coefficients of `e`
  intro k hk
  have h5 := hklt k hk
  rw [hFcoeff, hattain0, hFcoeff 0, pow_zero, mul_one] at h5
  exact h5

/-- Polynomial form of `dominant_const_of_isUnit`. -/
theorem dominant_const_of_isUnit_toRestricted (hdiv : MemDivisibleValueGroup K c)
    {e : Polynomial K} (he : IsUnit (Polynomial.toRestricted c e)) :
    ∀ k, 1 ≤ k → ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖ := by
  intro k hk
  have h := dominant_const_of_isUnit hdiv he k hk
  rwa [show PowerSeries.coeff k (Polynomial.toRestricted c e).1 = e.coeff k from
      Polynomial.coeff_coe e k,
    show PowerSeries.coeff 0 (Polynomial.toRestricted c e).1 = e.coeff 0 from
      Polynomial.coeff_coe e 0] at h

end FieldParameter

/-! ## §6  Bridge to the Newton-polygon file (to be done in `PhD/Main/Test/test.lean`, not here)

`NewtonPolygon.exists_factor_of_distinguished` follows from
`weierstrassPreparation_polynomial_divisible` by pure translation (import direction:
`test.lean` will import this file):

* its hypotheses `hle`/`hlt` are `distinguishedGen norm c (toRestricted c f).1 s` unbundled into
  coefficient norms (`‖f.coeff k‖ * c ^ k ≤ / < ‖f.coeff s‖ * c ^ s`; over a field the unit
  coefficient of `distinguished` is just nonvanishing);
* `IsUnit (Polynomial.toRestricted c e)` unbundles to the dominant-constant-coefficient form
  `∀ k ≥ 1, ‖e.coeff k‖ c ^ k < ‖e.coeff 0‖` via the unit characterisation of the restricted
  ring (the `he'_unit` step inside `WPrep.lean` / `ResUnits.lean`; blueprint Lemma 4.19);
* monicity of `ω` is discarded, and the two Gauss-norm attainment clauses of the conclusion
  follow from `‖toRestricted c ω‖ = c ^ s` and `distinguished_of_monic_gen`;
* `MemDivisibleValueGroup` here and in `test.lean` are the same predicate (to be unified);
* **`[CompleteSpace K]` must be added** to `exists_factor_of_distinguished` — and is thereby
  inherited by 5.5/5.7/5.10/5.11 — see the caution in the module docstring.
-/
