import PhD.WeierstrassPrep.WPrep_gen

-- see `PhD/ToPR/RestrictedIso.lean`: needed since the v4.33 bump for the `Restricted`
-- `Subring.toRing`/`toCommRing` instance diamond.
set_option backward.isDefEq.respectTransparency false

/-!
# Weierstrass division and preparation over `MvRestricted` (blueprint)

**Goal (rung 2 of `WPrep_gen.lean`, in its eventual home).**  Prove Weierstrass division and
preparation for the multivariate restricted power series ring `MvPowerSeries.Restricted R c`,
`c : Fin (n + 1) → ℝ` a radius tuple, for series *distinguished in one chosen variable* `X 0` —
first at radii realised in the value group (in particular `c = 1`), then at radii in the
divisible closure (`MemDivisibleValueGroup` in each coordinate).

**Strategy: transport along `RestrictedIso`.**  `MvRestricted.finSuccEquiv` (in
`PhD/ToPR/RestrictedIso.lean`) is an isometric ring isomorphism

  `Φ : MvPowerSeries.Restricted R c ≃+* PowerSeries.Restricted T (c 0)`,
  `T := MvPowerSeries.Restricted R (Fin.tail c)`

splitting off the variable `X 0`.  The right-hand side is exactly the shape of the `_gen`
theorems of `WPrep_gen.lean` §3, instantiated at the base ring `T` — the "Tate algebra" in the
remaining variables — and parameter `c 0`.  So the plan is *not* to re-run any of the analytic
arguments: it is to

1. verify that `T` satisfies the instance package the `_gen` theorems demand (§1),
2. build the (small) transport dictionary along `Φ` (§2),
3. discharge the scaling hypotheses `hα`/`h`/`hunit` over `T` from a field bottom (§3),
4. state the multivariate endpoints and prove them by transport (§4),
5. redo rung 2 (base change along a finite isometric extension of the bottom field, descent
   by uniqueness) at the multivariate level, where the argument is variable-count-agnostic
   (§5).

The two regimes the file must cover (per the original note here): the tuple `c = 1`, where
every scaling hypothesis is witnessed by `u = 1` and `distinguishedGen` degenerates to
`distinguished`; and general `c` with each `c i` in the divisible closure of the value group
of the bottom field, which needs §5.

## What already exists

From `PhD/ToPR/RestrictedIso.lean`:
* `MvRestricted.finSuccEquiv R n c` — the ring isomorphism `Φ` above;
* `MvRestricted_finSuccEquiv_norm_eq_norm` / `finSuccIsometry` / `finSuccIsometry'` — `Φ` is a
  Gauss-norm isometry (this is what carries `distinguishedGen`, the division bounds, and the
  norm normalisation `‖ω‖ = (c 0) ^ s` back and forth);
* `MvRestricted.coeff_finSuccEquiv` / `map_finSuccEquiv` — coefficients of `Φ f` are the
  `X 0`-slices of `f` (via `MvPowerSeries.finSuccEquiv` and `Finsupp.cons`);
* `foo` / `foo_isom` — the `n = 0` collapse `MvRestricted R (Fin 0 → ℝ) ≃ R`, the induction
  base for instances and the consistency check of §6;
* `MvRestricted.isCompleteSpace` — completeness of `MvRestricted R c` (needs
  `[CompleteSpace R]`);
* the `StrongPos` instances for `fun _ : Unit ↦ c 0` and `Fin.tail c`.

From `WPrep_gen.lean` §3, over an abstract base `(R', c')` (to be instantiated at `(T, c 0)`):
* unit-free: `weierstrassDivision_bounds_q_gen` / `_r_gen`, `weierstrassDivision_q_unique_gen`,
  `distinguished_of_monic_gen`;
* with `hα`/`h`/`hunit`: `weierstrassDivision_existance_gen` / `_uniqueness_gen` /
  `_polynomial_gen`, `weierstrassPreparation_exists_gen` / `_unique_gen` / `_polynomial_gen`.

From `Restricted_powerbounded_topnil.lean`: `MvPowerSeries.Restricted.normMulClass` — the Gauss
norm on `MvRestricted R' c'` is multiplicative given `[NormMulClass R'] [LinearOrder σ]`.

## Section plan

* **§0 (below, real code)** — the two anchor definitions: `distinguishedMvGen` (distinguished
  in `X 0`, *defined* by transport along `Φ`) and `Polynomial.toMvRestrictedX0` (the
  multivariate incarnation of an `X 0`-polynomial with coefficients in `T`).  Everything else
  in the file is stated in terms of these.

* **§1 Instance package for `T = MvRestricted R (Fin.tail c)`.**  The `_gen` theorems need,
  for the base ring `T`:
  - `NormedCommRing T` — `MvRestricted.isNormedRing` exists; check/add the `Comm` packaging
    (cf. `Restricted.isNormedCommRing` in the one-variable file);
  - `IsUltrametricDist T` — exists (`MvRestricted.isUltrametricDist`);
  - `CompleteSpace T` — exists (`MvRestricted.isCompleteSpace`, from `[CompleteSpace R]`);
  - `NormMulClass T` — `MvPowerSeries.Restricted.normMulClass` at `σ = Fin n` (needs
    `[NormMulClass R]`; `LinearOrder (Fin n)` is free);
  - `NormOneClass T` — to add: `‖C 1‖ = 1`, cf. the `local instance` in `WPrep.lean` (and the
    standing TODO there to prove it once for `MvRestricted`);
  - `Nontrivial T` — to add (trivial, via `C`);
  - `Filter.NeBot (𝓝[≠] (0 : T))` — to add: push small nonzero elements of `R` through the
    isometric constants map `C`, exactly as the `local instance` for
    `PowerSeries.Restricted R 1` in `WPrep.lean`;
  - `StrongPos (fun _ : Unit ↦ c 0)` — exists (RestrictedIso).
  Once these are in place, **every §3 statement of `WPrep_gen.lean` is available over
  `(T, c 0)` with no new analysis**.

* **§2 Transport dictionary along `Φ`.**  Small lemmas, all definitional unwinding plus the
  isometry:
  - `Polynomial.toMvRestrictedX0` commutes with the ring structure it needs to
    (`map_add`/`map_mul` through `Φ.symm` and `toRestricted` are already lemmas; record the
    composites used);
  - norms: `‖Polynomial.toMvRestrictedX0 n c ω‖ = ‖Polynomial.toRestricted (c 0) ω‖` (immediate
    from the isometry — this converts the preparation normalisation `‖ω‖ = (c 0) ^ s`);
  - units: `IsUnit (Φ.symm x) ↔ IsUnit x` (free, `Φ` is a ring isomorphism);
  - intrinsic slices (optional but desirable for consumers): unfold `distinguishedMvGen` to
    conditions on the `X 0`-slice coefficients of `f` itself via
    `MvRestricted.coeff_finSuccEquiv` and `MvPowerSeries.coeff_coeff_finSuccEquiv`
    (`Finsupp.cons` bookkeeping): the `s`-th slice is a unit of `T`, its weighted Gauss term
    `‖slice_s‖ (c 0)^s` attains `‖f‖`, and strictly dominates all later slices.

* **§3 Scaling hypotheses over the Tate algebra (field bottom `K`).**  Here `R = K` is a
  complete nontrivially-normed ultrametric field and `T = MvRestricted K (Fin.tail c)`.
  Under the value-group hypothesis
      `hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i`
  discharge, mirroring `exists_norm_inv_unit_gen`:
  - `hα` over `T` at `c 0`: the constant `C x₀` is a unit of `T` of norm `c 0`;
  - `hunit`: for `0 ≠ F : PowerSeries.Restricted T (c 0)`, the Gauss norm is attained twice
    over (`Restricted.gaussNorm_achieved'` at `c 0`, then `MvRestricted.gaussNorm_achieved`
    for the attaining coefficient in `T`), so
    `‖F‖ = ‖λ‖ · ∏ᵢ cᵢ^{tᵢ} · (c 0)^k ∈ ‖Kˣ‖` by `hc`; invert inside `Kˣ` and take the
    constant `C (λ'⁻¹)`.  (As in the one-variable file, `h` for a specific `g` follows from
    `hunit` and `g ≠ 0`, so only `hunit` needs work.)
  At the tuple `c = 1` the hypothesis `hc` is witnessed by `x = 1` throughout — the `c = 1`
  regime is *not* a separate development, just this instantiation.

* **§4 Rung-1 endpoints (radii in the value group).**  Statements over the field bottom `K`,
  proofs by: push `f, g` through `Φ`, apply the `(T, c 0)`-instance of the corresponding
  `_gen` theorem of §3 of `WPrep_gen.lean` with the hypotheses of §3 above, pull the output
  back through `Φ.symm` (quotients via `Φ.symm`, polynomial data via
  `Polynomial.toMvRestrictedX0`, norms via the isometry, units via the ring isomorphism).
  Target signatures:

      theorem mvWeierstrassDivision_uniqueness (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
          (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s)
          (f : MvPowerSeries.Restricted K c) :
          ∃! q : MvPowerSeries.Restricted K c,
          ∃! r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
            r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 n c r

      theorem mvWeierstrassPreparation_unique (hc : …) (g …) (s …) (gd …) :
          ∃! ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
          ∃! e : MvPowerSeries.Restricted K c, ω.Monic ∧ ω.degree = s ∧
            ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
            g = e * Polynomial.toMvRestrictedX0 n c ω

  plus the existence forms, the unit-free `mvWeierstrassDivision_bounds_q/_r` and
  `mvWeierstrassDivision_q_unique` (transport of the `_gen` bounds — these need **no** `hc`
  and are the workhorses of the §5 descent), and the `_polynomial` refinements (quotient/unit
  a polynomial in `X 0`; the polynomial-division statement needs the same
  `degree ≤ s` caveat as `weierstrassDivision_polynomial`).

* **§5 Rung 2 (radii in the divisible closure).**  Mirror §4–§5 of `WPrep_gen.lean` at the
  multivariate level, where (per the generality note there) the argument is
  variable-count-agnostic because everything happens coefficientwise over the bottom field:
  - hypothesis: `hdiv : ∀ i, MemDivisibleValueGroup K (c i)`;
  - **one extension for all radii**: inside `AlgebraicClosure K` adjoin roots
    `α₀, …, αₙ` with `αᵢ^{nᵢ} = xᵢ`, `‖xᵢ‖ = cᵢ^{nᵢ}`; `L = K⟮α₀, …, αₙ⟯` is finite over `K`,
    complete and isometric for the spectral norm, and realises every `c i` as a unit norm
    (cf. the single-`α` construction in `weierstrassDivision_existance_divisible`);
  - **base change**: `MvRestricted.mapAlgebra : MvRestricted K c →+* MvRestricted L c`,
    coefficientwise `algebraMap`, isometric by `hiso` — the `Fin (n+1) →₀ ℕ`-indexed clone of
    `Restricted.mapAlgebra`; record that it intertwines the two `finSuccEquiv`s (so §4 over
    `L` really is the univariate `_gen` machinery over `T_L`);
  - **descent by uniqueness**: the clone of `weierstrassDivision_descend` — pick a bounded
    `K`-linear retraction `π : L →ₗ[K] K` (finite-dimensionality over the complete `K`),
    apply it to every multivariate coefficient; the retraction of the `L`-division of
    `K`-data is a `K`-division (the `lmap_mul` computation is identical with
    `Finsupp`-antidiagonals), and the difference is an `L`-division of `0`, killed by the
    unit-free bounds of §4.  No Galois theory, no separability;
  - endpoints `mvWeierstrassDivision_*_divisible` / `mvWeierstrassPreparation_*_divisible`,
    with no `hc`/`h`/`hunit` hypotheses, exactly parallel to §5 of `WPrep_gen.lean`
    (preparation recovered from the descended division of `X 0 ^ s` by `g`, unit-ness of the
    descended quotient via the clone of `isUnit_of_isUnit_mapAlgebra`).

* **§6 Consistency and consumers.**
  - `n = 0` sanity check: through `foo_isom`, `T ≅ K` and the §4/§5 endpoints must literally
    recover the one-variable `_gen`/`_divisible` theorems of `WPrep_gen.lean` — worth stating
    once as a test;
  - the intended consumer is the multivariate Newton-polygon/factorisation theory (and, per
    the `WPrep_gen.lean` §4 note, the case `R = Restricted S`, i.e. univariate over a Tate
    algebra, is the `n = 1` instance of this file — no separate development needed);
  - once stable, the one-variable §4–§5 of `WPrep_gen.lean` become the `σ = Unit`/`n = 0`
    shadow of this file and can be refactored away (later decision, as with `c = 1`).

## Caution: an instance diamond, and how this file lives with it

§1 installs `MvRestricted.isNormedCommRing` on `MvPowerSeries.Restricted R d`.  Its
`toNormedRing` field is *definitionally* `MvRestricted.isNormedRing` (whose ring structure is
the original `Subring.toRing (MvPowerSeries.isSubring d)`), so no mathematical ambiguity is
created — every path produces the same ring, definitionally.  But typeclass resolution now
has **two syntactically different routes** to `Ring`/`Semiring` on the Tate algebra (and
hence to the instance arguments buried inside `MvPowerSeries.coeff`, `PowerSeries.coeff`,
`gaussNorm`, `‖·‖`, …): the pre-§1 route `Subring.toRing (isSubring d)`, used by everything
compiled *before* this file (`PhD/ToPR/MvRestricted.lean`, `PhD/ToPR/RestrictedIso.lean`),
and the post-§1 route `isNormedCommRing.toCommRing.toRing`, preferred by typeclass search
*inside and after* this file.  The two are definitionally equal at default transparency but
**not** at reducible transparency, with two practical consequences:

* `rw`/`simp` against a statement **elaborated in a pre-§1 file** (e.g.
  `MvRestricted.coeff_finSuccEquiv`, `Polynomial.coeff_coe` at Tate-algebra coefficients) can
  fail with "did not find an occurrence of the pattern" even though the displayed terms are
  pixel-identical — the mismatch sits in the invisible instance arguments, and `rw`'s keyed
  matching only unfolds reducibly.  The convention used throughout this file: consume such
  cross-file equations as *terms* (`exact`, `calc` steps, `congrArg`, `Eq.symm`), where
  unification works up to full definitional equality, or realign the goal with `show`;
  reserve `rw`/`simp` for equations stated in *this* file (all post-§1, hence mutually
  consistent) and for generic Mathlib lemmas (whose instance arguments are metavariables
  that unify with whatever the goal carries).

* The diamond is harmless for correctness, but it should eventually be **removed at the
  source**: move the §1 instances upstream into `PhD/ToPR/MvRestricted.lean`, directly after
  `MvRestricted.isNormedRing` — then every downstream file elaborates with one canonical
  path (this also mirrors the one-variable `Restricted.lean`, which declares its
  `CommRing`/`NormedCommRing` instances at the definition site).  When that migration
  happens, the term-mode workarounds here can be simplified back to `rw`s.

## Suggested order of work

1. §1 instances (`NormOneClass`, `Nontrivial`, `NeBot 𝓝[≠] 0`, `NormedCommRing` packaging).
2. §2 dictionary (norm of `toMvRestrictedX0`; unit transport; slice unfolding can wait).
3. §3 `hunit` over `T` (the only genuinely new *proof* at rung 1: double norm-attainment).
4. §4 endpoints by transport (mechanical, mirrors §3 of `WPrep_gen.lean` transporting along
   `rescaleEquiv` — same shape, different isomorphism).
5. §5 base change + descent (clone of `WPrep_gen.lean` §4–§5 with `Finsupp` bookkeeping).
6. §6 the `n = 0` consistency test.
-/

open Topology

/-! ## §0  Anchors: `distinguishedMvGen` and `X 0`-polynomials

Both are *defined* through the splitting isomorphism `Φ = MvRestricted.finSuccEquiv`, so that
every later statement transports definitionally; intrinsic (coefficientwise) characterisations
are §2 lemmas, not definitions. -/

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] (n : ℕ) (c : Fin (n + 1) → ℝ)
  [StrongPos c]

/-- `f` is **distinguished in the variable `X 0` of degree `s` at the radius tuple `c`**:
its image under the splitting isomorphism `MvRestricted.finSuccEquiv` — a univariate
restricted series over the Tate algebra `T = MvRestricted R (Fin.tail c)` in the remaining
variables — is `distinguishedGen` of degree `s` at parameter `c 0`.

Intrinsically (§2): the `X 0 ^ s`-slice of `f` is a unit of `T`, its weighted Gauss term
attains `‖f‖`, and it strictly dominates every higher slice. -/
def distinguishedMvGen (f : MvPowerSeries.Restricted R c) (s : ℕ) : Prop :=
  distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv R n c f).1 s

/-- The multivariate restricted series attached to a **polynomial in `X 0`** with coefficients
in the Tate algebra `T = MvRestricted R (Fin.tail c)` of the remaining variables: embed as a
univariate restricted series over `T` and pull back through the splitting isomorphism.

This is the shape of the remainder `r` in multivariate Weierstrass division and of the
distinguished factor `ω` in multivariate preparation. -/
noncomputable def Polynomial.toMvRestrictedX0
    (ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    MvPowerSeries.Restricted R c :=
  (MvRestricted.finSuccEquiv R n c).symm (Polynomial.toRestricted (c 0) ω)

/-! ## §1  Instance package for the coefficient Tate algebra

The `_gen` theorems of `WPrep_gen.lean` §3, over a base ring `S` at parameter `c 0`, require
`[NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [NormMulClass S] [NormOneClass S]
[Filter.NeBot (𝓝[≠] (0 : S))] [Nontrivial S]`.  This section provides the missing instances
for `S = MvPowerSeries.Restricted R d`, at a general index type `σ` except for completeness
(`σ = Fin m`, by induction through `RestrictedIso`).  Generality in `σ` matters: the
coefficient Tate algebra `T = MvRestricted R (Fin.tail c)` has index `Fin n` with *variable*
`n`, so the `Fin (n + 1)`-keyed instances of `RestrictedIso.lean` do not fire for it.

Already available and firing at general `σ`: `MvRestricted.isNormedRing`,
`MvRestricted.isUltrametricDist`, `MvPowerSeries.Restricted.normMulClass` (any
`[LinearOrder σ]`, from `[NormMulClass R]`; note this currently rests on the sorried
`MvRestricted.bar`), and the `StrongPos` instances.  The section ends with `example`s checking
that the complete package resolves — in particular for `MvRestricted R (Fin.tail c)` itself.

Everything here is a general `MvRestricted` fact; it can migrate to
`PhD/ToPR/MvRestricted.lean` when that file is refactored (it discharges the standing TODO in
`WPrep.lean` about proving `NormOneClass` once for `MvRestricted`). -/

namespace MvRestricted

section InstancePackage

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] {σ : Type*} (d : σ → ℝ)

/-- Constants as restricted multivariate power series (cf. `PowerSeries.Restricted.C`). -/
noncomputable def C (a : S) : MvPowerSeries.Restricted S d :=
  ⟨MvPowerSeries.C a, MvPowerSeries.isRestricted_C d a⟩

@[simp] lemma C_coe (a : S) : (MvRestricted.C d a).1 = MvPowerSeries.C a := rfl

lemma C_one : MvRestricted.C d (1 : S) = 1 :=
  Subtype.ext (map_one MvPowerSeries.C)

lemma C_mul (a b : S) :
    MvRestricted.C d (a * b) = MvRestricted.C d a * MvRestricted.C d b :=
  Subtype.ext (map_mul MvPowerSeries.C a b)

/-- Units of the coefficient ring give (constant) units of the Tate algebra. -/
lemma isUnit_C {a : S} (h : IsUnit a) : IsUnit (MvRestricted.C d a) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨MvRestricted.C d ↑u, MvRestricted.C d ↑u⁻¹,
    by rw [← MvRestricted.C_mul, u.mul_inv, MvRestricted.C_one],
    by rw [← MvRestricted.C_mul, u.inv_mul, MvRestricted.C_one]⟩, rfl⟩

variable [StrongPos d]

/-- The Gauss norm of a constant is the norm of the constant: the only nonzero Gauss term
sits at exponent `0`, with weight `∏ᵢ dᵢ⁰ = 1`. -/
@[simp] lemma norm_C (a : S) : ‖MvRestricted.C d a‖ = ‖a‖ := by
  classical
  rw [MvRestricted.norm_eq, C_coe]
  refine le_antisymm (ciSup_le fun t => ?_) ?_
  · by_cases ht : t = (0 : σ →₀ ℕ)
    · subst ht
      simp [MvPowerSeries.coeff_zero_C]
    · simp [MvPowerSeries.coeff_C, ht, norm_nonneg]
  · have h := MvPowerSeries.le_gaussNorm norm d (MvRestricted.C d a).1
      (MvRestricted.hasGaussNorm d (MvRestricted.C d a)) 0
    simpa [MvPowerSeries.coeff_zero_C] using h

/-- The Gauss norm is a norm of *commutative* ring: multiplication of restricted series is
that of the ambient `MvPowerSeries σ S`. -/
noncomputable instance isNormedCommRing : NormedCommRing (MvPowerSeries.Restricted S d) where
  toNormedRing := MvRestricted.isNormedRing S d
  mul_comm f g := Subtype.ext (mul_comm f.1 g.1)

instance normOneClass [NormOneClass S] : NormOneClass (MvPowerSeries.Restricted S d) where
  norm_one := by
    have h1 : (1 : MvPowerSeries.Restricted S d) = MvRestricted.C d 1 :=
      Subtype.ext (map_one MvPowerSeries.C).symm
    rw [h1, MvRestricted.norm_C]
    exact norm_one

instance nontrivial [Nontrivial S] : Nontrivial (MvPowerSeries.Restricted S d) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne S
  refine nontrivial_of_ne (MvRestricted.C d (x - y)) 0 fun h => sub_ne_zero.mpr hxy ?_
  rw [← norm_eq_zero, ← MvRestricted.norm_C d (x - y), h, norm_zero]

/-- Nonzero elements of arbitrarily small norm in the coefficient ring give the same in the
Tate algebra, via constants (cf. the `local instance` for `PowerSeries.Restricted R 1` in
`WPrep.lean`). -/
instance nhdsNE_neBot [Filter.NeBot (𝓝[≠] (0 : S))] :
    Filter.NeBot (𝓝[≠] (0 : MvPowerSeries.Restricted S d)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr_ne, hr⟩ : ∃ r : S, r ≠ 0 ∧ ‖r‖ < ε := by
    have hS : (0 : S) ∈ closure ({0}ᶜ : Set S) :=
      mem_closure_iff_nhdsWithin_neBot.mpr inferInstance
    obtain ⟨r, hr_mem, hr_dist⟩ := Metric.mem_closure_iff.mp hS ε hε
    rw [dist_comm, dist_zero_right] at hr_dist
    exact ⟨r, hr_mem, hr_dist⟩
  have hne : MvRestricted.C d r ≠ 0 := fun h0 => hr_ne (norm_eq_zero.mp
    (by rw [← MvRestricted.norm_C d r, h0, norm_zero]))
  exact ⟨MvRestricted.C d r, hne, by
    rw [dist_comm, dist_zero_right, MvRestricted.norm_C]; exact hr⟩

end InstancePackage

section CompleteSpaceFin

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

/-- Completeness of the Tate algebra at any `Fin`-indexed radius tuple.  The instance
`MvRestricted.isCompleteSpace` of `RestrictedIso.lean` is keyed on the syntactic shape
`Fin (m + 1)`, so it cannot fire when the number of variables is a *variable* `m` (as it is
for `Fin.tail c : Fin n → ℝ`); this version covers every `m`, with the zero-variable collapse
`foo_isom : MvRestricted S (Fin 0 → ℝ) ≃ᵢ S` as base case. -/
instance completeSpace_finTuple {m : ℕ} (d : Fin m → ℝ) [StrongPos d] [CompleteSpace S] :
    CompleteSpace (MvPowerSeries.Restricted S d) := by
  cases m with
  | zero => exact (foo_isom d).completeSpace
  | succ k => exact MvRestricted.isCompleteSpace k d

end CompleteSpaceFin

section PackageCheck

/- The full §3-of-`WPrep_gen.lean` instance package resolves for the Tate algebra over a base
satisfying it (completeness at `Fin`-indexed tuples).  These `example`s are regression tests:
if an instance stops firing, the transport in §4 breaks here first, with a readable error. -/

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [NormMulClass S] [NormOneClass S]
  [Nontrivial S] [CompleteSpace S] [Filter.NeBot (𝓝[≠] (0 : S))]
  {m : ℕ} (d : Fin m → ℝ) [StrongPos d]

noncomputable example : NormedCommRing (MvPowerSeries.Restricted S d) := inferInstance
example : IsUltrametricDist (MvPowerSeries.Restricted S d) := inferInstance
example : CompleteSpace (MvPowerSeries.Restricted S d) := inferInstance
example : NormMulClass (MvPowerSeries.Restricted S d) := inferInstance
example : NormOneClass (MvPowerSeries.Restricted S d) := inferInstance
example : Nontrivial (MvPowerSeries.Restricted S d) := inferInstance
example : Filter.NeBot (𝓝[≠] (0 : MvPowerSeries.Restricted S d)) := inferInstance

end PackageCheck

section TailCheck

/- The instantiation §4 will actually use: the whole package fires for the coefficient Tate
algebra `T = MvRestricted R (Fin.tail c)` of the splitting isomorphism — whose variable count
`n` is a variable, the case the `Fin (m + 1)`-keyed instances miss — together with the
`StrongPos` instance at the split-off parameter `c 0`. -/

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [Nontrivial R] [CompleteSpace R] [Filter.NeBot (𝓝[≠] (0 : R))]
  (n : ℕ) (c : Fin (n + 1) → ℝ) [StrongPos c]

noncomputable example : NormedCommRing (MvPowerSeries.Restricted R (Fin.tail c)) :=
  inferInstance
example : IsUltrametricDist (MvPowerSeries.Restricted R (Fin.tail c)) := inferInstance
example : CompleteSpace (MvPowerSeries.Restricted R (Fin.tail c)) := inferInstance
example : NormMulClass (MvPowerSeries.Restricted R (Fin.tail c)) := inferInstance
example : NormOneClass (MvPowerSeries.Restricted R (Fin.tail c)) := inferInstance
example : Nontrivial (MvPowerSeries.Restricted R (Fin.tail c)) := inferInstance
example : Filter.NeBot (𝓝[≠] (0 : MvPowerSeries.Restricted R (Fin.tail c))) := inferInstance
example : StrongPos (fun _ : Unit ↦ c 0) := inferInstance

end TailCheck

end MvRestricted

/-! ## §2  Transport dictionary along the splitting isomorphism

The small definitional layer §4 consumes: the splitting isomorphism `Φ` is a Gauss-norm
isometry in both directions, transports units, and interacts with
`Polynomial.toMvRestrictedX0` exactly as `Polynomial.toRestricted` does on the univariate
side.  `coeff_toMvRestrictedX0` is the (light) intrinsic description promised in the
blueprint: the multivariate coefficients of an `X 0`-polynomial are the coefficients of its
`T`-coefficients at `Finsupp.cons`-split exponents.  (The full intrinsic unfolding of
`distinguishedMvGen` in terms of slice Gauss terms is deferred until a consumer needs it.) -/

section TransportDictionary

/-- `distinguishedMvGen` is definitionally the transported predicate. -/
lemma distinguishedMvGen_iff (f : MvPowerSeries.Restricted R c) (s : ℕ) :
    distinguishedMvGen n c f s ↔
      distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv R n c f).1 s :=
  Iff.rfl

/-- The `Φ.symm` form of `distinguishedMvGen_iff` (the direction §4 uses): a pulled-back
univariate series is distinguished in `X 0` iff the original is `distinguishedGen` at
parameter `c 0`. -/
lemma distinguishedMvGen_finSuccEquiv_symm
    (x : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) (s : ℕ) :
    distinguishedMvGen n c ((MvRestricted.finSuccEquiv R n c).symm x) s ↔
      distinguishedGen norm (c 0) x.1 s := by
  unfold distinguishedMvGen
  rw [RingEquiv.apply_symm_apply]

/-- The splitting isomorphism is a Gauss-norm isometry: restatement of
`MvRestricted_finSuccEquiv_norm_eq_norm` in terms of the ring norms. -/
lemma MvRestricted.norm_finSuccEquiv (f : MvPowerSeries.Restricted R c) :
    ‖MvRestricted.finSuccEquiv R n c f‖ = ‖f‖ :=
  MvRestricted_finSuccEquiv_norm_eq_norm R n c f

/-- The inverse of the splitting isomorphism is a Gauss-norm isometry. -/
lemma MvRestricted.norm_finSuccEquiv_symm
    (x : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) :
    ‖(MvRestricted.finSuccEquiv R n c).symm x‖ = ‖x‖ := by
  have h := MvRestricted.norm_finSuccEquiv n c ((MvRestricted.finSuccEquiv R n c).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- Units transport along the inverse of the splitting isomorphism (used to pull the unit `e`
of a Weierstrass preparation back to `MvRestricted`). -/
lemma MvRestricted.isUnit_finSuccEquiv_symm_iff
    (x : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) :
    IsUnit ((MvRestricted.finSuccEquiv R n c).symm x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map (MvRestricted.finSuccEquiv R n c),
    fun h => h.map (MvRestricted.finSuccEquiv R n c).symm⟩

/-- `Φ` sends an `X 0`-polynomial to the corresponding univariate polynomial over the
coefficient Tate algebra — the identity converting statements about
`Polynomial.toRestricted` data into statements about `Polynomial.toMvRestrictedX0`. -/
lemma MvRestricted.finSuccEquiv_toMvRestrictedX0
    (ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    MvRestricted.finSuccEquiv R n c (Polynomial.toMvRestrictedX0 n c ω) =
      Polynomial.toRestricted (c 0) ω :=
  (MvRestricted.finSuccEquiv R n c).apply_symm_apply _

namespace Polynomial

@[simp] lemma toMvRestrictedX0_zero :
    toMvRestrictedX0 n c (0 : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) = 0 := by
  unfold toMvRestrictedX0
  rw [toRestricted_zero]
  exact map_zero _

@[simp] lemma toMvRestrictedX0_one :
    toMvRestrictedX0 n c (1 : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) = 1 := by
  unfold toMvRestrictedX0
  rw [show toRestricted (c 0)
      (1 : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) = 1 from
    Subtype.ext coe_one]
  exact map_one _

@[simp] lemma toMvRestrictedX0_add
    (ω₁ ω₂ : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    toMvRestrictedX0 n c (ω₁ + ω₂) = toMvRestrictedX0 n c ω₁ + toMvRestrictedX0 n c ω₂ := by
  unfold toMvRestrictedX0
  rw [toRestricted_add]
  exact map_add _ _ _

@[simp] lemma toMvRestrictedX0_sub
    (ω₁ ω₂ : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    toMvRestrictedX0 n c (ω₁ - ω₂) = toMvRestrictedX0 n c ω₁ - toMvRestrictedX0 n c ω₂ := by
  unfold toMvRestrictedX0
  rw [toRestricted_sub]
  exact map_sub _ _ _

@[simp] lemma toMvRestrictedX0_mul
    (ω₁ ω₂ : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    toMvRestrictedX0 n c (ω₁ * ω₂) = toMvRestrictedX0 n c ω₁ * toMvRestrictedX0 n c ω₂ := by
  unfold toMvRestrictedX0
  rw [toRestricted_mul]
  exact map_mul _ _ _

/-- The norm of an `X 0`-polynomial is the norm of the corresponding univariate polynomial
over the coefficient Tate algebra: transports the preparation normalisation
`‖ω‖ = (c 0) ^ s`. -/
lemma norm_toMvRestrictedX0 (ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c))) :
    ‖toMvRestrictedX0 n c ω‖ = ‖toRestricted (c 0) ω‖ :=
  MvRestricted.norm_finSuccEquiv_symm n c _

/-- Injectivity: `∃!` statements transport through `toMvRestrictedX0`. -/
lemma toMvRestrictedX0_injective :
    Function.Injective (toMvRestrictedX0 (R := R) n c) := fun ω₁ ω₂ h => by
  have h1 := congrArg (MvRestricted.finSuccEquiv R n c) h
  rw [MvRestricted.finSuccEquiv_toMvRestrictedX0, MvRestricted.finSuccEquiv_toMvRestrictedX0]
    at h1
  exact coe_inj.mp (congrArg Subtype.val h1)

/-- Intrinsic coefficient description of an `X 0`-polynomial: its multivariate coefficient at
an exponent `t` is the `Finsupp.tail t`-coefficient of the coefficient of `ω` in `X 0`-degree
`t 0`. -/
lemma coeff_toMvRestrictedX0 (ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)))
    (t : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff t (toMvRestrictedX0 n c ω).1 =
      MvPowerSeries.coeff (Finsupp.tail t) ((ω.coeff (t 0)).1) := by
  have hval : (toMvRestrictedX0 n c ω).1 = (MvPowerSeries.finSuccEquiv R n).symm
      (PowerSeries.map (MvPowerSeries.isSubring (R := R) (Fin.tail c)).subtype
        (toRestricted (c 0) ω).1) := by
    have h := MvRestricted.map_finSuccEquiv n c (toMvRestrictedX0 n c ω)
    rw [MvRestricted.finSuccEquiv_toMvRestrictedX0] at h
    exact (AlgEquiv.eq_symm_apply _).mpr h.symm
  rw [hval, MvPowerSeries.funSuccEquivSymm_coeff, PowerSeries.coeff_map]
  exact congrArg (fun z : MvPowerSeries.Restricted R (Fin.tail c) =>
    MvPowerSeries.coeff (Finsupp.tail t) z.1) (coeff_coe ω (t 0))

end Polynomial

end TransportDictionary

/-! ## §3  Scaling hypotheses over the Tate algebra (field bottom)

Over a field bottom `K`, with every radius realised in the value group
(`hc : ∀ i, ∃ x : Kˣ, ‖x‖ = c i`), the `hα`/`h`/`hunit` hypotheses of the `_gen` theorems
become theorems over the coefficient Tate algebra `T = MvRestricted K (Fin.tail c)`:

* `exists_unit_norm_tate` (`hα`): a constant realises `c 0` as the norm of a unit of `T`;
* `exists_norm_inv_unit_tate` (`hunit`; the `h` hypothesis for a specific `g ≠ 0` is the
  special case): the Gauss norm of a nonzero restricted series over `T` is attained twice
  over — once in the `X 0`-index (`Restricted.gaussNorm_achieved'`), once in the remaining
  exponents (`MvRestricted.gaussNorm_achieved`) — so `‖F‖ = ‖λ‖ · ∏ᵢ cᵢ^{tᵢ} · (c 0)^k` is
  the norm of an explicit product of units of `K`, and its inverse is realised by a constant.

At the tuple `c = 1` the hypothesis `hc` is witnessed by `x = 1` throughout: the `c = 1`
regime is this instantiation, not a separate development.  Completeness and nontriviality of
`K` are not needed here — only multiplicativity of its norm. -/

section ScalingHypotheses

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The `hα` hypothesis over the Tate algebra.**  If `c 0` is the norm of a unit of `K`,
then it is the norm of a unit — a constant — of `MvRestricted K (Fin.tail c)`. -/
lemma exists_unit_norm_tate (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i) :
    ∃ u : (MvPowerSeries.Restricted K (Fin.tail c))ˣ,
      ‖(u : MvPowerSeries.Restricted K (Fin.tail c))‖ = c 0 := by
  obtain ⟨x, hx⟩ := hc 0
  obtain ⟨u, hu⟩ := MvRestricted.isUnit_C (Fin.tail c) x.isUnit
  exact ⟨u, by rw [hu, MvRestricted.norm_C, hx]⟩

/-- **The `hunit` hypothesis over the Tate algebra.**  With every radius in the value group of
`K`, the norm of a nonzero restricted series over `T = MvRestricted K (Fin.tail c)` is
inverted by a unit of `T` (a constant). -/
lemma exists_norm_inv_unit_tate (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (F : PowerSeries.Restricted (MvPowerSeries.Restricted K (Fin.tail c)) (c 0))
    (hF : F ≠ 0) :
    ∃ a : MvPowerSeries.Restricted K (Fin.tail c), ‖a‖ = ‖F‖⁻¹ ∧ IsUnit a := by
  have hc0 : (0 : ℝ) < c 0 := StrongPos_pos c 0
  choose x hx using hc
  -- attain the Gauss norm of `F` in the `X 0`-index
  obtain ⟨k, hk⟩ := Restricted.gaussNorm_achieved' (c 0) hc0.le F
  have hnormF : ‖F‖ = ‖PowerSeries.coeff k F.1‖ * (c 0) ^ k := Eq.symm hk
  have hcoeffk : PowerSeries.coeff k F.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hnormF
    exact (norm_pos_iff.mpr hF).ne' hnormF
  -- attain the Gauss norm of the attaining `T`-coefficient in the remaining exponents
  obtain ⟨t, ht⟩ := MvRestricted.gaussNorm_achieved (Fin.tail c)
    (MvRestricted.test (Fin.tail c) (StrongPos_pos (Fin.tail c))) (PowerSeries.coeff k F.1)
  have hnormT : ‖PowerSeries.coeff k F.1‖ =
      ‖MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1‖ * t.prod (Fin.tail c · ^ ·) :=
    Eq.symm ht
  have hlam : MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hnormT
    exact hcoeffk (norm_eq_zero.mp hnormT)
  -- `‖F‖` is the norm of an explicit product of units of `K`
  have hprod : ‖∏ i ∈ t.support, (x i.succ : K) ^ t i‖ = t.prod (Fin.tail c · ^ ·) := by
    show _ = ∏ i ∈ t.support, Fin.tail c i ^ t i
    rw [show ‖∏ i ∈ t.support, (x i.succ : K) ^ t i‖ =
        ∏ i ∈ t.support, ‖(x i.succ : K) ^ t i‖ from map_prod (normHom : K →*₀ ℝ) _ _]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ‖(x i.succ : K) ^ t i‖ = c i.succ ^ t i
    rw [norm_pow, hx i.succ]
  have hna : ‖MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1 * (x 0 : K) ^ k *
      ∏ i ∈ t.support, (x i.succ : K) ^ t i‖ = ‖F‖ := by
    rw [norm_mul, norm_mul, norm_pow, hx 0, hprod, hnormF, hnormT]
    ring
  have ha_ne : MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1 * (x 0 : K) ^ k *
      ∏ i ∈ t.support, (x i.succ : K) ^ t i ≠ 0 :=
    mul_ne_zero (mul_ne_zero hlam (pow_ne_zero _ (x 0).ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (x i.succ).ne_zero)
  refine ⟨MvRestricted.C (Fin.tail c) (MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1 *
      (x 0 : K) ^ k * ∏ i ∈ t.support, (x i.succ : K) ^ t i)⁻¹, ?_,
    MvRestricted.isUnit_C (Fin.tail c) (isUnit_iff_ne_zero.mpr (inv_ne_zero ha_ne))⟩
  rw [MvRestricted.norm_C, norm_inv, hna]

end ScalingHypotheses

/-! ## §4  Multivariate endpoints (radii in the value group)

Weierstrass division and preparation on `MvRestricted K c`, for series distinguished in `X 0`,
over a complete ultrametric field bottom `K` with every radius realised in the value group
(`hc : ∀ i, ∃ x : Kˣ, ‖x‖ = c i` — witnessed by `x = 1` throughout at the tuple `c = 1`).

Every proof is transport: push the data through the splitting isomorphism `Φ`, apply the
`(T, c 0)`-instance of the corresponding `_gen` theorem of `WPrep_gen.lean` §3 (its instance
package is §1, its scaling hypotheses are §3), and pull the output back through the §2
dictionary.  The bounds and quotient-uniqueness need no `hc` — their `_gen` sources are
unit-free — which is what the descent of §5 will rely on. -/

section MvEndpoints

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- `NeBot (𝓝[≠] (0 : K))` holds in any nontrivially normed field but is not an instance in
-- Mathlib; the §1 instance then lifts it to the coefficient Tate algebra.
local instance : Filter.NeBot (𝓝[≠] (0 : K)) := NormedField.nhdsNE_neBot 0

-- multiplicativity of the Gauss norm on the univariate side of the splitting isomorphism
-- (a `local instance` in `WPrep_gen.lean` too, so not importable).
local instance : NormMulClass
    (PowerSeries.Restricted (MvPowerSeries.Restricted K (Fin.tail c)) (c 0)) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ c 0)

omit [CompleteSpace K] in
/-- **Division bound for the quotient** (unit-free; cf.
`weierstrassDivision_bounds_q_gen`). -/
lemma mvWeierstrassDivision_bounds_q (g : MvPowerSeries.Restricted K c) (s : ℕ)
    (hg : distinguishedMvGen n c g s) (f q : MvPowerSeries.Restricted K c)
    (r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + Polynomial.toMvRestrictedX0 n c r) : ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  have hg' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := hg
  have hf' : MvRestricted.finSuccEquiv K n c f = MvRestricted.finSuccEquiv K n c g *
      MvRestricted.finSuccEquiv K n c q + Polynomial.toRestricted (c 0) r := by
    rw [hf, map_add, map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
  have h_bd := weierstrassDivision_bounds_q_gen (MvRestricted.finSuccEquiv K n c g) s hg'
    (MvRestricted.finSuccEquiv K n c f) (MvRestricted.finSuccEquiv K n c q) r hr hf'
  rwa [MvRestricted.norm_finSuccEquiv, MvRestricted.norm_finSuccEquiv,
    MvRestricted.norm_finSuccEquiv] at h_bd

omit [CompleteSpace K] in
/-- **Division bound for the remainder** (unit-free; cf.
`weierstrassDivision_bounds_r_gen`). -/
lemma mvWeierstrassDivision_bounds_r (g : MvPowerSeries.Restricted K c) (s : ℕ)
    (hg : distinguishedMvGen n c g s) (f q : MvPowerSeries.Restricted K c)
    (r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + Polynomial.toMvRestrictedX0 n c r) :
    ‖Polynomial.toMvRestrictedX0 n c r‖ ≤ ‖f‖ := by
  have hg' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := hg
  have hf' : MvRestricted.finSuccEquiv K n c f = MvRestricted.finSuccEquiv K n c g *
      MvRestricted.finSuccEquiv K n c q + Polynomial.toRestricted (c 0) r := by
    rw [hf, map_add, map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
  have h_bd := weierstrassDivision_bounds_r_gen (MvRestricted.finSuccEquiv K n c g) s hg'
    (MvRestricted.finSuccEquiv K n c f) (MvRestricted.finSuccEquiv K n c q) r hr hf'
  rw [Polynomial.norm_toMvRestrictedX0]
  rwa [MvRestricted.norm_finSuccEquiv] at h_bd

omit [CompleteSpace K] in
/-- **The quotient of a multivariate Weierstrass division is unique** (unit-free; cf.
`weierstrassDivision_q_unique_gen`). -/
lemma mvWeierstrassDivision_q_unique (g : MvPowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedMvGen n c g s) (f : MvPowerSeries.Restricted K c)
    {q₁ q₂ : MvPowerSeries.Restricted K c}
    {r₁ r₂ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))}
    (hr₁ : Polynomial.degree r₁ < s) (hf₁ : f = g * q₁ + Polynomial.toMvRestrictedX0 n c r₁)
    (hr₂ : Polynomial.degree r₂ < s) (hf₂ : f = g * q₂ + Polynomial.toMvRestrictedX0 n c r₂) :
    q₁ = q₂ := by
  have gd' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := gd
  have hf₁' : MvRestricted.finSuccEquiv K n c f = MvRestricted.finSuccEquiv K n c g *
      MvRestricted.finSuccEquiv K n c q₁ + Polynomial.toRestricted (c 0) r₁ := by
    rw [hf₁, map_add, map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
  have hf₂' : MvRestricted.finSuccEquiv K n c f = MvRestricted.finSuccEquiv K n c g *
      MvRestricted.finSuccEquiv K n c q₂ + Polynomial.toRestricted (c 0) r₂ := by
    rw [hf₂, map_add, map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
  exact (MvRestricted.finSuccEquiv K n c).injective
    (weierstrassDivision_q_unique_gen (MvRestricted.finSuccEquiv K n c g) s gd'
      (MvRestricted.finSuccEquiv K n c f) hr₁ hf₁' hr₂ hf₂')

/-- **Multivariate Weierstrass division, existence.** -/
theorem mvWeierstrassDivision_existance (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s)
    (f : MvPowerSeries.Restricted K c) :
    ∃ (q : MvPowerSeries.Restricted K c)
      (r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))),
      Polynomial.degree r < s ∧ f = g * q + Polynomial.toMvRestrictedX0 n c r := by
  have gd' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := gd
  have hgne : MvRestricted.finSuccEquiv K n c g ≠ 0 := fun h0 => gd'.ne_zero (by rw [h0]; rfl)
  obtain ⟨q', r', hr', hf'⟩ := weierstrassDivision_existance_gen (exists_unit_norm_tate n c hc)
    (MvRestricted.finSuccEquiv K n c g) s gd' (MvRestricted.finSuccEquiv K n c f)
    (exists_norm_inv_unit_tate n c hc _ hgne)
    (fun F hF => exists_norm_inv_unit_tate n c hc F hF)
  refine ⟨(MvRestricted.finSuccEquiv K n c).symm q', r', hr', ?_⟩
  have h2 := congrArg (MvRestricted.finSuccEquiv K n c).symm hf'
  rw [RingEquiv.symm_apply_apply, map_add, map_mul, RingEquiv.symm_apply_apply] at h2
  exact h2

/-- **Multivariate Weierstrass division, existence and uniqueness.** -/
theorem mvWeierstrassDivision_uniqueness (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s)
    (f : MvPowerSeries.Restricted K c) :
    ∃! q : MvPowerSeries.Restricted K c,
    ∃! r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
      Polynomial.degree r < s ∧ f = g * q + Polynomial.toMvRestrictedX0 n c r := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := mvWeierstrassDivision_existance n c hc g s gd f
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.toMvRestrictedX0_injective n c (add_left_cancel (hf'.symm.trans hf₀))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact mvWeierstrassDivision_q_unique n c g s gd f hr' hf' hr₀ hf₀

/-- **Multivariate Weierstrass preparation, existence**: `g = e · ω` with `ω` a monic
`X 0`-polynomial of degree `s` and `e` a unit of `MvRestricted K c`. -/
theorem mvWeierstrassPreparation_exists (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s) :
    ∃ (ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)))
      (e : MvPowerSeries.Restricted K c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 n c ω := by
  have gd' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := gd
  obtain ⟨ω, e', ωm, ωd, ωn, he', hg'⟩ := weierstrassPreparation_exists_gen
    (exists_unit_norm_tate n c hc) (MvRestricted.finSuccEquiv K n c g) s gd'
    (fun F hF => exists_norm_inv_unit_tate n c hc F hF)
  refine ⟨ω, (MvRestricted.finSuccEquiv K n c).symm e', ωm, ωd, ?_,
    (MvRestricted.isUnit_finSuccEquiv_symm_iff n c e').mpr he', ?_⟩
  · rw [Polynomial.norm_toMvRestrictedX0]
    exact ωn
  · have h2 := congrArg (MvRestricted.finSuccEquiv K n c).symm hg'
    rw [RingEquiv.symm_apply_apply, map_mul] at h2
    exact h2

/-- **Multivariate Weierstrass preparation, existence and uniqueness.** -/
theorem mvWeierstrassPreparation_unique (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s) :
    ∃! ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! e : MvPowerSeries.Restricted K c, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 n c ω := by
  have gd' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c g).1 s := gd
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg'⟩, he_uniq⟩, hω_uniq⟩ :=
    weierstrassPreparation_unique_gen (exists_unit_norm_tate n c hc)
      (MvRestricted.finSuccEquiv K n c g) s gd'
      (fun F hF => exists_norm_inv_unit_tate n c hc F hF)
  have hgMv : g = (MvRestricted.finSuccEquiv K n c).symm e *
      Polynomial.toMvRestrictedX0 n c ω := by
    have h2 := congrArg (MvRestricted.finSuccEquiv K n c).symm hg'
    rw [RingEquiv.symm_apply_apply, map_mul] at h2
    exact h2
  refine ⟨ω, ⟨(MvRestricted.finSuccEquiv K n c).symm e,
    ⟨ωm, ωd, by rw [Polynomial.norm_toMvRestrictedX0]; exact ωn,
      (MvRestricted.isUnit_finSuccEquiv_symm_iff n c e).mpr he, hgMv⟩, ?_⟩, ?_⟩
  · -- the unit is unique for the fixed factor `ω`
    rintro e' ⟨-, -, -, hu', hg''⟩
    have h3 : MvRestricted.finSuccEquiv K n c g = MvRestricted.finSuccEquiv K n c e' *
        Polynomial.toRestricted (c 0) ω := by
      rw [hg'', map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
    have h4 : MvRestricted.finSuccEquiv K n c e' = e :=
      he_uniq _ ⟨ωm, ωd, ωn, hu'.map (MvRestricted.finSuccEquiv K n c), h3⟩
    rw [← h4, RingEquiv.symm_apply_apply]
  · -- the factor `ω` is unique
    rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg''⟩, -⟩
    rw [Polynomial.norm_toMvRestrictedX0] at ω'n
    have h3 : MvRestricted.finSuccEquiv K n c g = MvRestricted.finSuccEquiv K n c e' *
        Polynomial.toRestricted (c 0) ω' := by
      rw [hg'', map_mul, MvRestricted.finSuccEquiv_toMvRestrictedX0]
    refine hω_uniq ω' ⟨MvRestricted.finSuccEquiv K n c e',
      ⟨ω'm, ω'd, ω'n, hu'.map (MvRestricted.finSuccEquiv K n c), h3⟩, ?_⟩
    rintro e'' ⟨-, -, -, -, hg'''⟩
    have hsub : (e'' - MvRestricted.finSuccEquiv K n c e') *
        Polynomial.toRestricted (c 0) ω' = 0 := by
      rw [sub_mul, ← hg''', ← h3, sub_self]
    have hn0 : ‖e'' - MvRestricted.finSuccEquiv K n c e'‖ *
        ‖Polynomial.toRestricted (c 0) ω'‖ = 0 := by
      rw [← norm_mul, hsub, norm_zero]
    rw [ω'n] at hn0
    rcases mul_eq_zero.mp hn0 with h' | h'
    · exact sub_eq_zero.mp (norm_eq_zero.mp h')
    · exact absurd h' (pow_pos (StrongPos_pos c 0) s).ne'

/-- **Multivariate Weierstrass division for `X 0`-polynomials** (cf.
`weierstrassDivision_polynomial_gen`; the hypothesis `hgs` is necessary for the same reason
as in one variable). -/
theorem mvWeierstrassDivision_polynomial (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) (s : ℕ)
    (gd : distinguishedMvGen n c (Polynomial.toMvRestrictedX0 n c g₀) s)
    (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) :
    ∃! q : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
      Polynomial.degree r < s ∧ Polynomial.toMvRestrictedX0 n c f₀ =
        Polynomial.toMvRestrictedX0 n c g₀ * Polynomial.toMvRestrictedX0 n c q +
        Polynomial.toMvRestrictedX0 n c r := by
  have gd' : distinguishedGen norm (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h1 : distinguishedGen norm (c 0)
        (MvRestricted.finSuccEquiv K n c (Polynomial.toMvRestrictedX0 n c g₀)).1 s := gd
    rwa [MvRestricted.finSuccEquiv_toMvRestrictedX0] at h1
  have hgne : Polynomial.toRestricted (c 0) g₀ ≠ 0 := fun h0 => gd'.ne_zero (by rw [h0]; rfl)
  obtain ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, -⟩, -⟩ := weierstrassDivision_polynomial_gen
    (exists_unit_norm_tate n c hc) g₀ s gd' hgs f₀
    (exists_norm_inv_unit_tate n c hc _ hgne)
    (fun F hF => exists_norm_inv_unit_tate n c hc F hF)
  have hf₀Mv : Polynomial.toMvRestrictedX0 n c f₀ = Polynomial.toMvRestrictedX0 n c g₀ *
      Polynomial.toMvRestrictedX0 n c q₀ + Polynomial.toMvRestrictedX0 n c r₀ := by
    have h2 := congrArg (MvRestricted.finSuccEquiv K n c).symm hf₀
    rw [map_add, map_mul] at h2
    exact h2
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀Mv⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.toMvRestrictedX0_injective n c (add_left_cancel (hf'.symm.trans hf₀Mv))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.toMvRestrictedX0_injective n c
      (mvWeierstrassDivision_q_unique n c (Polynomial.toMvRestrictedX0 n c g₀) s gd
        (Polynomial.toMvRestrictedX0 n c f₀) hr' hf' hr₀ hf₀Mv)

/-- **Multivariate Weierstrass preparation for `X 0`-polynomials** (cf.
`weierstrassPreparation_polynomial_gen`): the unit `e` is itself an `X 0`-polynomial.  As in
one variable, `IsUnit (Polynomial.toMvRestrictedX0 n c e)` is unit-ness in the restricted
ring, not in the polynomial ring. -/
theorem mvWeierstrassPreparation_polynomial (hc : ∀ i, ∃ x : Kˣ, ‖(x : K)‖ = c i)
    (g₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) (s : ℕ)
    (gd : distinguishedMvGen n c (Polynomial.toMvRestrictedX0 n c g₀) s) :
    ∃! ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! e : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧
      IsUnit (Polynomial.toMvRestrictedX0 n c e) ∧
      Polynomial.toMvRestrictedX0 n c g₀ =
        Polynomial.toMvRestrictedX0 n c e * Polynomial.toMvRestrictedX0 n c ω := by
  have gd' : distinguishedGen norm (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h1 : distinguishedGen norm (c 0)
        (MvRestricted.finSuccEquiv K n c (Polynomial.toMvRestrictedX0 n c g₀)).1 s := gd
    rwa [MvRestricted.finSuccEquiv_toMvRestrictedX0] at h1
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg'⟩, he_uniq⟩, hω_uniq⟩ :=
    weierstrassPreparation_polynomial_gen (exists_unit_norm_tate n c hc) g₀ s gd'
      (fun F hF => exists_norm_inv_unit_tate n c hc F hF)
  have hgMv : Polynomial.toMvRestrictedX0 n c g₀ =
      Polynomial.toMvRestrictedX0 n c e * Polynomial.toMvRestrictedX0 n c ω := by
    have h2 := congrArg (MvRestricted.finSuccEquiv K n c).symm hg'
    rw [map_mul] at h2
    exact h2
  refine ⟨ω, ⟨e, ⟨ωm, ωd, by rw [Polynomial.norm_toMvRestrictedX0]; exact ωn,
    (MvRestricted.isUnit_finSuccEquiv_symm_iff n c _).mpr he, hgMv⟩, ?_⟩, ?_⟩
  · -- the polynomial unit is unique for the fixed factor `ω`
    rintro e' ⟨-, -, -, hu', hg''⟩
    have hg''uni : Polynomial.toRestricted (c 0) g₀ =
        Polynomial.toRestricted (c 0) e' * Polynomial.toRestricted (c 0) ω := by
      have h2 := congrArg (MvRestricted.finSuccEquiv K n c) hg''
      rwa [MvRestricted.finSuccEquiv_toMvRestrictedX0, map_mul,
        MvRestricted.finSuccEquiv_toMvRestrictedX0,
        MvRestricted.finSuccEquiv_toMvRestrictedX0] at h2
    exact he_uniq e' ⟨ωm, ωd, ωn,
      (MvRestricted.isUnit_finSuccEquiv_symm_iff n c _).mp hu', hg''uni⟩
  · -- the factor `ω` is unique
    rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg''⟩, he'_uniq⟩
    have hg''uni : Polynomial.toRestricted (c 0) g₀ =
        Polynomial.toRestricted (c 0) e' * Polynomial.toRestricted (c 0) ω' := by
      have h2 := congrArg (MvRestricted.finSuccEquiv K n c) hg''
      rwa [MvRestricted.finSuccEquiv_toMvRestrictedX0, map_mul,
        MvRestricted.finSuccEquiv_toMvRestrictedX0,
        MvRestricted.finSuccEquiv_toMvRestrictedX0] at h2
    refine hω_uniq ω' ⟨e', ⟨ω'm, ω'd,
      by rw [← Polynomial.norm_toMvRestrictedX0]; exact ω'n,
      (MvRestricted.isUnit_finSuccEquiv_symm_iff n c _).mp hu', hg''uni⟩, ?_⟩
    rintro e'' ⟨-, -, -, hu'', hg'''⟩
    refine he'_uniq e'' ⟨ω'm, ω'd, ω'n,
      (MvRestricted.isUnit_finSuccEquiv_symm_iff n c _).mpr hu'', ?_⟩
    have h3 := congrArg (MvRestricted.finSuccEquiv K n c).symm hg'''
    rw [map_mul] at h3
    exact h3

end MvEndpoints

/-! ## §5  Rung 2: base change (radii in the divisible closure)

The plan (mirroring §4–§5 of `WPrep_gen.lean`, variable-count-agnostically): for radii only in
the divisible closure (`hdiv : ∀ i, MemDivisibleValueGroup K (c i)`), adjoin roots
`α₀, …, αₙ` with `αᵢ^{nᵢ} = xᵢ` inside `AlgebraicClosure K` to get one finite isometric
complete extension `L` realising *every* `c i` as a unit norm; run §4 over `L`; descend by
uniqueness.

This section provides the **base-change layer**: the coefficientwise embedding
`MvRestricted.mapAlgebra : MvRestricted K d →+* MvRestricted L d` (any index type — the
descent needs it at both `c` and `Fin.tail c`), its isometry and injectivity, its
intertwining with the splitting isomorphism (`coeff_finSuccEquiv_mapAlgebra`), compatibility
with `X 0`-polynomials, and the transport of `distinguishedMvGen` (only the `K → L` direction
is needed: units map to units, and all Gauss terms are preserved by the isometry).

The rest of §5 follows below: **descent by uniqueness** (`mvWeierstrassDivision_descend`,
with the coefficientwise-retraction layer, and `isUnit_of_isUnit_mapAlgebraMv`), and the
**endpoints `_divisible`** — no `hc`/`h`/`hunit` hypotheses: one finite extension
`L = K(α₀, …, αₙ)` inside `AlgebraicClosure K` realises every radius as a unit norm
(spectral norm, isometric by `spectralNorm_extends`, complete by finite dimensionality),
§4 runs over `L` via `distinguishedMvGen_mapAlgebra`, and the result descends; the
preparation recovers `ω` over `K` from the descended division of `(X 0) ^ s` by `g`,
with unit-ness of the descended quotient transported by `isUnit_of_isUnit_mapAlgebraMv`. -/

section BaseChangeGeneral

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (L : Type*) [NormedField L] [IsUltrametricDist L] [Algebra K L]
  {σ : Type*} (d : σ → ℝ)

omit [IsUltrametricDist K] [IsUltrametricDist L] in
private lemma isRestricted_mapAlgebraMv (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : MvPowerSeries σ K} (hf : MvPowerSeries.IsRestricted d f) :
    MvPowerSeries.IsRestricted d (MvPowerSeries.map (algebraMap K L) f) :=
  Filter.Tendsto.congr (fun t => by rw [MvPowerSeries.coeff_map, hiso]) hf

/-- **Base change of restricted multivariate power series** along an isometric embedding
`K ↪ L` (coefficientwise `algebraMap`; cf. `Restricted.mapAlgebra` in `WPrep_gen.lean`). -/
noncomputable def MvRestricted.mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    MvPowerSeries.Restricted K d →+* MvPowerSeries.Restricted L d :=
  RingHom.codRestrict
    ((MvPowerSeries.map (algebraMap K L)).comp (MvPowerSeries.isSubring (R := K) d).subtype)
    (MvPowerSeries.isSubring (R := L) d)
    (fun f => isRestricted_mapAlgebraMv L d hiso f.2)

lemma MvRestricted.mapAlgebra_coe (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : MvPowerSeries.Restricted K d) :
    (MvRestricted.mapAlgebra L d hiso f).1 = MvPowerSeries.map (algebraMap K L) f.1 := rfl

/-- Base change is a Gauss-norm isometry (termwise, by `hiso`). -/
lemma MvRestricted.norm_mapAlgebra [StrongPos d] (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : MvPowerSeries.Restricted K d) :
    ‖MvRestricted.mapAlgebra L d hiso f‖ = ‖f‖ := by
  show MvPowerSeries.gaussNorm norm d (MvPowerSeries.map (algebraMap K L) f.1) =
    MvPowerSeries.gaussNorm norm d f.1
  unfold MvPowerSeries.gaussNorm
  exact iSup_congr fun t => by rw [MvPowerSeries.coeff_map, hiso]

lemma MvRestricted.mapAlgebra_injective [StrongPos d]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    Function.Injective (MvRestricted.mapAlgebra L d hiso) := fun x y h => by
  have h1 : ‖x - y‖ = 0 := by
    rw [← MvRestricted.norm_mapAlgebra L d hiso (x - y), map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

end BaseChangeGeneral

section BaseChangeSplit

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (L : Type*) [NormedField L] [IsUltrametricDist L] [Algebra K L]

omit [IsUltrametricDist K] [IsUltrametricDist L] [Algebra K L] in
/-- The raw splitting isomorphism intertwines coefficientwise base change. -/
private lemma finSuccEquiv_map (φ : K →+* L) (F : MvPowerSeries (Fin (n + 1)) K) :
    MvPowerSeries.finSuccEquiv L n (MvPowerSeries.map φ F) =
      PowerSeries.map (MvPowerSeries.map φ) (MvPowerSeries.finSuccEquiv K n F) := by
  refine PowerSeries.ext fun j => MvPowerSeries.ext fun i => ?_
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_map,
    PowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_coeff_finSuccEquiv]

/-- The coefficients of the split base-changed series are the base changes of the split
coefficients: `Φ_L ∘ mapAlgebra = (coefficientwise mapAlgebra) ∘ Φ_K`. -/
lemma MvRestricted.coeff_finSuccEquiv_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : MvPowerSeries.Restricted K c) (j : ℕ) :
    PowerSeries.coeff j
        (MvRestricted.finSuccEquiv L n c (MvRestricted.mapAlgebra L c hiso f)).1 =
      MvRestricted.mapAlgebra L (Fin.tail c) hiso
        (PowerSeries.coeff j (MvRestricted.finSuccEquiv K n c f).1) := by
  refine Subtype.ext ?_
  calc (PowerSeries.coeff j (MvRestricted.finSuccEquiv L n c
          (MvRestricted.mapAlgebra L c hiso f)).1).1
      = PowerSeries.coeff j (MvPowerSeries.finSuccEquiv L n
          (MvRestricted.mapAlgebra L c hiso f).1) :=
        MvRestricted.coeff_finSuccEquiv n c (MvRestricted.mapAlgebra L c hiso f) j
    _ = PowerSeries.coeff j (PowerSeries.map (MvPowerSeries.map (algebraMap K L))
          (MvPowerSeries.finSuccEquiv K n f.1)) := by
        rw [show (MvRestricted.mapAlgebra L c hiso f).1 =
            MvPowerSeries.map (algebraMap K L) f.1 from rfl,
          finSuccEquiv_map n L (algebraMap K L) f.1]
    _ = MvPowerSeries.map (algebraMap K L)
          (PowerSeries.coeff j (MvPowerSeries.finSuccEquiv K n f.1)) := by
        rw [PowerSeries.coeff_map]
    _ = (MvRestricted.mapAlgebra L (Fin.tail c) hiso
          (PowerSeries.coeff j (MvRestricted.finSuccEquiv K n c f).1)).1 :=
        congrArg (MvPowerSeries.map (algebraMap K L))
          (MvRestricted.coeff_finSuccEquiv n c f j).symm

/-- Base change commutes with the `X 0`-polynomial embedding: coefficientwise, both sides
are `algebraMap` applied at `Finsupp.cons`-split exponents. -/
lemma MvRestricted.mapAlgebra_toMvRestrictedX0 (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) :
    MvRestricted.mapAlgebra L c hiso (Polynomial.toMvRestrictedX0 n c ω) =
      Polynomial.toMvRestrictedX0 n c
        (ω.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso)) := by
  refine Subtype.ext (MvPowerSeries.ext fun t => ?_)
  rw [MvRestricted.mapAlgebra_coe, MvPowerSeries.coeff_map,
    Polynomial.coeff_toMvRestrictedX0, Polynomial.coeff_toMvRestrictedX0,
    Polynomial.coeff_map, MvRestricted.mapAlgebra_coe, MvPowerSeries.coeff_map]

/-- `distinguishedMvGen` is preserved by base change (the `K → L` direction, which is what
running §4 over the extension needs): the distinguished coefficient maps to a unit, and every
Gauss term is preserved by the isometry. -/
lemma distinguishedMvGen_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : MvPowerSeries.Restricted K c} {s : ℕ} (hf : distinguishedMvGen n c f s) :
    distinguishedMvGen n c (MvRestricted.mapAlgebra L c hiso f) s := by
  have hf' : distinguishedGen norm (c 0) (MvRestricted.finSuccEquiv K n c f).1 s := hf
  obtain ⟨h1, h2, h3⟩ := hf'
  show distinguishedGen norm (c 0)
    (MvRestricted.finSuccEquiv L n c (MvRestricted.mapAlgebra L c hiso f)).1 s
  refine ⟨?_, ?_, ?_⟩
  · rw [MvRestricted.coeff_finSuccEquiv_mapAlgebra n c L hiso f s]
    exact h1.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso)
  · have e1 : PowerSeries.gaussNorm norm (c 0) (MvRestricted.finSuccEquiv L n c
        (MvRestricted.mapAlgebra L c hiso f)).1 =
        PowerSeries.gaussNorm norm (c 0) (MvRestricted.finSuccEquiv K n c f).1 :=
      calc PowerSeries.gaussNorm norm (c 0) (MvRestricted.finSuccEquiv L n c
            (MvRestricted.mapAlgebra L c hiso f)).1
          = ‖MvRestricted.finSuccEquiv L n c (MvRestricted.mapAlgebra L c hiso f)‖ :=
            (Restricted.norm_eq (c 0) _).symm
        _ = ‖MvRestricted.mapAlgebra L c hiso f‖ := MvRestricted.norm_finSuccEquiv n c _
        _ = ‖f‖ := MvRestricted.norm_mapAlgebra L c hiso f
        _ = ‖MvRestricted.finSuccEquiv K n c f‖ := (MvRestricted.norm_finSuccEquiv n c f).symm
        _ = PowerSeries.gaussNorm norm (c 0) (MvRestricted.finSuccEquiv K n c f).1 :=
            Restricted.norm_eq (c 0) _
    rw [e1, MvRestricted.coeff_finSuccEquiv_mapAlgebra n c L hiso f s,
      MvRestricted.norm_mapAlgebra]
    exact h2
  · intro t ht
    rw [MvRestricted.coeff_finSuccEquiv_mapAlgebra n c L hiso f t,
      MvRestricted.coeff_finSuccEquiv_mapAlgebra n c L hiso f s,
      MvRestricted.norm_mapAlgebra, MvRestricted.norm_mapAlgebra]
    exact h3 t ht

end BaseChangeSplit

/-! ### §5, continued: descent by uniqueness

The multivariate clone of `weierstrassDivision_descend`.  A bounded `K`-linear retraction
`π : L →ₗ[K] K` of the embedding (it exists because `L` is a finite-dimensional space over
the complete field `K`), applied to every multivariate coefficient, carries `MvRestricted L d`
back to `MvRestricted K d`; it retracts the base change, is multiplicative against
base-changed factors (`retractRaw_mul`, the `lmap_mul` computation with `Finsupp`
antidiagonals), and preserves restrictedness (squeeze against the bound of `π`).  Applied to
an `L`-division of `K`-data it produces a `K`-division; the difference of the two
`L`-divisions is a division of `0`, killed by the unit-free bounds of §4. -/

section RetractRaw

variable {K : Type*} [NormedField K] {L : Type*} [NormedField L] [Algebra K L] {σ : Type*}

/-- The coefficientwise retraction of a multivariate power series along `π`. -/
private def retractRaw (π : L →ₗ[K] K) (F : MvPowerSeries σ L) : MvPowerSeries σ K :=
  fun t => π (MvPowerSeries.coeff t F)

private lemma coeff_retractRaw (π : L →ₗ[K] K) (F : MvPowerSeries σ L) (t : σ →₀ ℕ) :
    MvPowerSeries.coeff t (retractRaw π F) = π (MvPowerSeries.coeff t F) := rfl

private lemma retractRaw_zero (π : L →ₗ[K] K) :
    retractRaw π (0 : MvPowerSeries σ L) = 0 := by
  refine MvPowerSeries.ext fun t => ?_
  rw [coeff_retractRaw]
  simp

private lemma retractRaw_add (π : L →ₗ[K] K) (F G : MvPowerSeries σ L) :
    retractRaw π (F + G) = retractRaw π F + retractRaw π G := by
  refine MvPowerSeries.ext fun t => ?_
  simp only [coeff_retractRaw, map_add]

/-- The retraction undoes coefficientwise base change. -/
private lemma retractRaw_map (π : L →ₗ[K] K) (hπ : ∀ a : K, π (algebraMap K L a) = a)
    (F : MvPowerSeries σ K) :
    retractRaw π (MvPowerSeries.map (algebraMap K L) F) = F := by
  refine MvPowerSeries.ext fun t => ?_
  rw [coeff_retractRaw, MvPowerSeries.coeff_map, hπ]

private lemma retractRaw_one (π : L →ₗ[K] K) (hπ : ∀ a : K, π (algebraMap K L a) = a) :
    retractRaw π (1 : MvPowerSeries σ L) = 1 := by
  rw [show (1 : MvPowerSeries σ L) = MvPowerSeries.map (algebraMap K L) 1 from
    (map_one (MvPowerSeries.map (algebraMap K L))).symm, retractRaw_map π hπ]

/-- The `lmap_mul` computation: the retraction pulls a product with a base-changed series
back to a product over `K` — termwise on `Finsupp` antidiagonals,
`π (algebraMap (Gₐ) · H_b) = Gₐ · π (H_b)` by `K`-linearity. -/
private lemma retractRaw_mul (π : L →ₗ[K] K) (G : MvPowerSeries σ K)
    (H : MvPowerSeries σ L) :
    retractRaw π (MvPowerSeries.map (algebraMap K L) G * H) = G * retractRaw π H := by
  classical
  refine MvPowerSeries.ext fun t => ?_
  rw [coeff_retractRaw, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MvPowerSeries.coeff_map, coeff_retractRaw, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The retraction of a restricted series is restricted: its Gauss terms are squeezed by
`Cπ` times those of the original. -/
private lemma isRestricted_retractRaw {d : σ → ℝ} [StrongPos d] (π : L →ₗ[K] K) {Cπ : ℝ}
    (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖) {F : MvPowerSeries σ L}
    (hF : MvPowerSeries.IsRestricted d F) :
    MvPowerSeries.IsRestricted d (retractRaw π F) := by
  have hprod0 : ∀ t : σ →₀ ℕ, 0 ≤ t.prod (d · ^ ·) := fun t =>
    Finset.prod_nonneg fun i _ => pow_nonneg (StrongPos_pos d i).le _
  have h0 : Filter.Tendsto (fun t : σ →₀ ℕ => Cπ * (‖MvPowerSeries.coeff t F‖ *
      t.prod (d · ^ ·))) Filter.cofinite (nhds 0) := by
    simpa using Filter.Tendsto.const_mul Cπ hF
  show Filter.Tendsto (fun t : σ →₀ ℕ => ‖MvPowerSeries.coeff t (retractRaw π F)‖ *
    t.prod (d · ^ ·)) Filter.cofinite (nhds 0)
  refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _) (hprod0 t)) (fun t => ?_) h0
  rw [coeff_retractRaw, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hCπ _) (hprod0 t)

/-- The coefficientwise retraction, on restricted series. -/
private def retract [IsUltrametricDist K] [IsUltrametricDist L] (d : σ → ℝ) [StrongPos d]
    (π : L →ₗ[K] K) {Cπ : ℝ} (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖)
    (x : MvPowerSeries.Restricted L d) : MvPowerSeries.Restricted K d :=
  ⟨retractRaw π x.1, isRestricted_retractRaw π hCπ x.2⟩

private lemma retract_coe [IsUltrametricDist K] [IsUltrametricDist L] (d : σ → ℝ)
    [StrongPos d] (π : L →ₗ[K] K) {Cπ : ℝ} (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖)
    (x : MvPowerSeries.Restricted L d) :
    (retract d π hCπ x).1 = retractRaw π x.1 := rfl

end RetractRaw

section Descent

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]

/-- **Descent by uniqueness (rung 2, core).**  A multivariate Weierstrass division over a
finite isometric extension `L`, of data defined over `K`, descends to `K` — the clone of
`weierstrassDivision_descend`, coefficientwise over the multivariate exponents. -/
lemma mvWeierstrassDivision_descend [Module.Finite K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (g : MvPowerSeries.Restricted K c) (s : ℕ)
    (gd : distinguishedMvGen n c g s) (f : MvPowerSeries.Restricted K c)
    {q : MvPowerSeries.Restricted L c}
    {r : Polynomial (MvPowerSeries.Restricted L (Fin.tail c))}
    (hr : Polynomial.degree r < s)
    (hf : MvRestricted.mapAlgebra L c hiso f =
      MvRestricted.mapAlgebra L c hiso g * q + Polynomial.toMvRestrictedX0 n c r) :
    ∃ (q₀ : MvPowerSeries.Restricted K c)
      (r₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))),
      Polynomial.degree r₀ < s ∧ f = g * q₀ + Polynomial.toMvRestrictedX0 n c r₀ ∧
      MvRestricted.mapAlgebra L c hiso q₀ = q ∧
      r₀.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso) = r := by
  -- a bounded `K`-linear retraction of the embedding
  letI : NormedSpace K L :=
    ⟨fun a x => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hπ : ∀ a : K, π (algebraMap K L a) = a := fun a => LinearMap.congr_fun hπcomp a
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  -- the candidate quotient and remainder over `K`
  set q₀ : MvPowerSeries.Restricted K c := retract c π hCπ q with hq₀def
  set r₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)) :=
    ∑ k ∈ r.support, Polynomial.monomial k (retract (Fin.tail c) π hCπ (r.coeff k))
    with hr₀def
  have hretract0 : retract (Fin.tail c) π hCπ
      (0 : MvPowerSeries.Restricted L (Fin.tail c)) = 0 := Subtype.ext (retractRaw_zero π)
  have hr₀coeff : ∀ m, r₀.coeff m = retract (Fin.tail c) π hCπ (r.coeff m) := by
    intro m
    by_cases hm : m ∈ r.support
    · rw [hr₀def, Polynomial.finsetSum_coeff,
        Finset.sum_eq_single_of_mem m hm (fun k _ hkm => by
          rw [Polynomial.coeff_monomial, if_neg hkm]),
        Polynomial.coeff_monomial, if_pos rfl]
    · rw [hr₀def, Polynomial.finsetSum_coeff,
        Finset.sum_eq_zero (fun k hks => by
          rw [Polynomial.coeff_monomial, if_neg (fun hkm : k = m => hm (hkm ▸ hks))]),
        show r.coeff m = 0 from by simpa [Polynomial.mem_support_iff] using hm]
      exact hretract0.symm
  have hr₀deg : r₀.degree < s := by
    rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
    intro m hm
    rw [hr₀coeff m, hr m hm]
    exact hretract0
  -- the `L`-level equation at the level of raw multivariate series
  have hf1 : MvPowerSeries.map (algebraMap K L) f.1 =
      MvPowerSeries.map (algebraMap K L) g.1 * q.1 +
      (Polynomial.toMvRestrictedX0 n c r).1 := by
    have h := congrArg Subtype.val hf
    rwa [show (MvRestricted.mapAlgebra L c hiso g * q +
        Polynomial.toMvRestrictedX0 n c r).1 =
        (MvRestricted.mapAlgebra L c hiso g).1 * q.1 +
        (Polynomial.toMvRestrictedX0 n c r).1 from rfl,
      MvRestricted.mapAlgebra_coe, MvRestricted.mapAlgebra_coe] at h
  -- the retraction of the `L`-remainder is the `K`-remainder
  have hX0 : retractRaw π (Polynomial.toMvRestrictedX0 n c r).1 =
      (Polynomial.toMvRestrictedX0 n c r₀).1 := by
    refine MvPowerSeries.ext fun t => ?_
    rw [coeff_retractRaw, Polynomial.coeff_toMvRestrictedX0,
      Polynomial.coeff_toMvRestrictedX0, hr₀coeff (t 0), retract_coe, coeff_retractRaw]
  -- applying the retraction coefficientwise gives the `K`-level division
  have hK : f = g * q₀ + Polynomial.toMvRestrictedX0 n c r₀ := by
    refine Subtype.ext ?_
    show f.1 = g.1 * retractRaw π q.1 + (Polynomial.toMvRestrictedX0 n c r₀).1
    have h2 := congrArg (retractRaw π) hf1
    rwa [retractRaw_map π hπ f.1, retractRaw_add, retractRaw_mul, hX0] at h2
  -- the difference of the two `L`-divisions is a division of `0`, killed by the bounds
  have hgd' : distinguishedMvGen n c (MvRestricted.mapAlgebra L c hiso g) s :=
    distinguishedMvGen_mapAlgebra n c L hiso gd
  have hzero : (0 : MvPowerSeries.Restricted L c) = MvRestricted.mapAlgebra L c hiso g *
      (q - MvRestricted.mapAlgebra L c hiso q₀) +
      Polynomial.toMvRestrictedX0 n c
        (r - r₀.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso)) := by
    have hmapK := congrArg (MvRestricted.mapAlgebra L c hiso) hK
    rw [map_add, map_mul, MvRestricted.mapAlgebra_toMvRestrictedX0] at hmapK
    rw [mul_sub, Polynomial.toMvRestrictedX0_sub]
    linear_combination hf - hmapK
  have hdegρ : (r - r₀.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso)).degree < s :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt hr (lt_of_le_of_lt Polynomial.degree_map_le hr₀deg))
  have hq_eq : q - MvRestricted.mapAlgebra L c hiso q₀ = 0 := by
    have hb := mvWeierstrassDivision_bounds_q n c (MvRestricted.mapAlgebra L c hiso g) s
      hgd' 0 _ _ hdegρ hzero
    simp only [norm_zero, mul_zero, norm_le_zero_iff] at hb
    exact hb
  have hr_eq : r - r₀.map (MvRestricted.mapAlgebra L (Fin.tail c) hiso) = 0 := by
    have hb := mvWeierstrassDivision_bounds_r n c (MvRestricted.mapAlgebra L c hiso g) s
      hgd' 0 _ _ hdegρ hzero
    simp only [norm_zero, norm_le_zero_iff] at hb
    refine Polynomial.toMvRestrictedX0_injective n c ?_
    rw [hb, Polynomial.toMvRestrictedX0_zero]
  exact ⟨q₀, r₀, hr₀deg, hK, (sub_eq_zero.mp hq_eq).symm, (sub_eq_zero.mp hr_eq).symm⟩

/-- **Unit-ness descends along isometric base change** (cf. `isUnit_of_isUnit_mapAlgebra`):
retract the inverse coefficientwise. -/
lemma isUnit_of_isUnit_mapAlgebraMv {σ : Type*} (d : σ → ℝ) [StrongPos d]
    [Module.Finite K L] (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {u : MvPowerSeries.Restricted K d}
    (h : IsUnit (MvRestricted.mapAlgebra L d hiso u)) : IsUnit u := by
  letI : NormedSpace K L :=
    ⟨fun a y => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hπ : ∀ a : K, π (algebraMap K L a) = a := fun a => LinearMap.congr_fun hπcomp a
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  obtain ⟨v, hv⟩ := h
  have hqv1 : MvPowerSeries.map (algebraMap K L) u.1 *
      ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) : MvPowerSeries.Restricted L d).1 = 1 := by
    have hqv : MvRestricted.mapAlgebra L d hiso u *
        ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) : MvPowerSeries.Restricted L d) = 1 := by
      rw [← hv, Units.mul_inv]
    have h1 := congrArg Subtype.val hqv
    rwa [show (MvRestricted.mapAlgebra L d hiso u *
        ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) : MvPowerSeries.Restricted L d)).1 =
        (MvRestricted.mapAlgebra L d hiso u).1 *
        ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) : MvPowerSeries.Restricted L d).1 from rfl,
      MvRestricted.mapAlgebra_coe] at h1
  have hone : u * retract d π hCπ ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) :
      MvPowerSeries.Restricted L d) = 1 := by
    apply Subtype.ext
    show u.1 * retractRaw π ((v⁻¹ : (MvPowerSeries.Restricted L d)ˣ) :
      MvPowerSeries.Restricted L d).1 = 1
    have h2 := congrArg (retractRaw π) hqv1
    rwa [retractRaw_mul, retractRaw_one π hπ] at h2
  exact IsUnit.of_mul_eq_one _ hone

end Descent

/-! ### §5, endpoints: division and preparation at radii in the divisible closure

The multivariate analogues of `WPrep_gen.lean` §5, with no `hc`/`h`/`hunit` hypotheses.  The
extension realising all `n + 1` radii at once is `L = K(α₀, …, αₙ)` inside
`AlgebraicClosure K` with `αᵢ^{mᵢ} = xᵢ`, `‖xᵢ‖ = cᵢ^{mᵢ}`: finite (finitely many integral
generators), complete, isometric and ultrametric for the spectral norm, with
`‖αᵢ‖ = c i` realised by units.  `extension_frame` packages this construction once; the two
`L`-dependent endpoints (division existence, preparation existence) are its continuations,
and the remaining four are `K`-level arguments on top of the unit-free §4 lemmas, exactly
parallel to the one-variable file. -/

section MvDivisible

universe uK

variable {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A monic `X 0`-polynomial of degree `s` with `‖ω‖ = (c 0) ^ s` is distinguished in `X 0`
of degree `s` (the multivariate `distinguished_of_monic_gen`). -/
lemma distinguishedMvGen_of_monic (ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)))
    (s : ℕ) (ωm : ω.Monic) (ωd : ω.degree = s)
    (ωn : ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s) :
    distinguishedMvGen n c (Polynomial.toMvRestrictedX0 n c ω) s :=
  (distinguishedMvGen_finSuccEquiv_symm n c (Polynomial.toRestricted (c 0) ω) s).mpr
    (distinguished_of_monic_gen ω s ωm ωd
      (by rw [← Polynomial.norm_toMvRestrictedX0]; exact ωn))

/-- One finite isometric complete extension of `K` realising **every** radius `c i` as the
norm of a unit: adjoin `mᵢ`-th roots `αᵢ` of elements of norm `cᵢ^{mᵢ}` inside the algebraic
closure, normed by the spectral norm.  Stated as an eliminator so the construction is done
once. -/
private lemma extension_frame (hdiv : ∀ i, MemDivisibleValueGroup K (c i)) {P : Prop}
    (h : ∀ (L : Type uK) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
      [Algebra K L] [Module.Finite K L],
      (∀ a : K, ‖algebraMap K L a‖ = ‖a‖) → (∀ i, ∃ u : Lˣ, ‖(u : L)‖ = c i) → P) : P := by
  have hc0 : ∀ i, (0 : ℝ) < c i := StrongPos_pos c
  choose m hm x hx using hdiv
  choose α hα using fun i => IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (x i)) (Nat.pos_of_ne_zero (hm i))
  have hmem : ∀ i, α i ∈ IntermediateField.adjoin K (Set.range α) := fun i =>
    IntermediateField.subset_adjoin K (Set.range α) ⟨i, rfl⟩
  haveI : Finite (Set.range α) := (Set.finite_range α).to_subtype
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K (Set.range α)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : Algebra.IsAlgebraic K ↥(IntermediateField.adjoin K (Set.range α)) :=
    Algebra.IsAlgebraic.of_finite K _
  letI : NontriviallyNormedField ↥(IntermediateField.adjoin K (Set.range α)) :=
    spectralNorm.nontriviallyNormedField K _
  haveI : IsUltrametricDist ↥(IntermediateField.adjoin K (Set.range α)) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hiso : ∀ a : K, ‖algebraMap K ↥(IntermediateField.adjoin K (Set.range α)) a‖ = ‖a‖ :=
    fun a => spectralNorm_extends a
  letI : NormedSpace K ↥(IntermediateField.adjoin K (Set.range α)) :=
    ⟨fun a y => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  haveI : CompleteSpace ↥(IntermediateField.adjoin K (Set.range α)) :=
    FiniteDimensional.complete K _
  have hgen : ∀ i, (⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α))) ^ m i =
      algebraMap K ↥(IntermediateField.adjoin K (Set.range α)) (x i) := fun i => by
    apply (algebraMap ↥(IntermediateField.adjoin K (Set.range α))
      (AlgebraicClosure K)).injective
    rw [map_pow, IntermediateField.algebraMap_apply,
      show ((⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α))) :
        AlgebraicClosure K) = α i from rfl,
      hα i, ← IsScalarTower.algebraMap_apply]
  have hnorm : ∀ i, ‖(⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α)))‖ = c i :=
    fun i => by
    refine (pow_left_inj₀ (norm_nonneg _) (hc0 i).le (hm i)).mp ?_
    rw [← norm_pow, hgen i, hiso, hx i]
  have hne : ∀ i, (⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α))) ≠ 0 :=
    fun i h0 => by
    have h1 := hnorm i
    rw [h0, norm_zero] at h1
    exact (hc0 i).ne h1
  exact h ↥(IntermediateField.adjoin K (Set.range α)) hiso
    (fun i => ⟨Units.mk0 _ (hne i), hnorm i⟩)

/-- **Multivariate Weierstrass division, existence, at divisible-closure radii.** -/
theorem mvWeierstrassDivision_existance_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s)
    (f : MvPowerSeries.Restricted K c) :
    ∃ (q : MvPowerSeries.Restricted K c)
      (r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))),
      Polynomial.degree r < s ∧ f = g * q + Polynomial.toMvRestrictedX0 n c r := by
  refine extension_frame n c hdiv ?_
  intro L _ _ _ _ _ hiso hcL
  obtain ⟨qL, rL, hrL, hfL⟩ := mvWeierstrassDivision_existance n c hcL
    (MvRestricted.mapAlgebra L c hiso g) s (distinguishedMvGen_mapAlgebra n c L hiso gd)
    (MvRestricted.mapAlgebra L c hiso f)
  obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ := mvWeierstrassDivision_descend n c L hiso g s gd f hrL hfL
  exact ⟨q₀, r₀, hr₀, heq⟩

/-- **Multivariate Weierstrass division, existence and uniqueness, at divisible-closure
radii.** -/
theorem mvWeierstrassDivision_uniqueness_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s)
    (f : MvPowerSeries.Restricted K c) :
    ∃! q : MvPowerSeries.Restricted K c,
    ∃! r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
      Polynomial.degree r < s ∧ f = g * q + Polynomial.toMvRestrictedX0 n c r := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := mvWeierstrassDivision_existance_divisible n c hdiv g s gd f
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.toMvRestrictedX0_injective n c (add_left_cancel (hf'.symm.trans hf₀))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact mvWeierstrassDivision_q_unique n c g s gd f hr' hf' hr₀ hf₀

/-- **Multivariate Weierstrass division for `X 0`-polynomials at divisible-closure radii**
(the hypothesis `hgs` is necessary for the same reason as in one variable). -/
theorem mvWeierstrassDivision_polynomial_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) (s : ℕ)
    (gd : distinguishedMvGen n c (Polynomial.toMvRestrictedX0 n c g₀) s)
    (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) :
    ∃! q : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! r : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
      Polynomial.degree r < s ∧ Polynomial.toMvRestrictedX0 n c f₀ =
        Polynomial.toMvRestrictedX0 n c g₀ * Polynomial.toMvRestrictedX0 n c q +
        Polynomial.toMvRestrictedX0 n c r := by
  -- `g₀` has degree exactly `s` with unit top coefficient in the Tate algebra, so rescaling
  -- makes it monic and polynomial division provides a polynomial solution
  have gd' : distinguishedGen norm (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h1 : distinguishedGen norm (c 0)
        (MvRestricted.finSuccEquiv K n c (Polynomial.toMvRestrictedX0 n c g₀)).1 s := gd
    rwa [MvRestricted.finSuccEquiv_toMvRestrictedX0] at h1
  have hgu : IsUnit (g₀.coeff s) := by
    have h1 : IsUnit (PowerSeries.coeff s
        (g₀ : PowerSeries (MvPowerSeries.Restricted K (Fin.tail c)))) := gd'.unit
    rwa [Polynomial.coeff_coe] at h1
  obtain ⟨u, hu⟩ := hgu
  have hdeg : g₀.degree = s :=
    le_antisymm hgs (Polynomial.le_degree_of_ne_zero (hu ▸ u.ne_zero))
  have hlead : g₀.leadingCoeff = g₀.coeff s :=
    congrArg g₀.coeff (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  have hmonic : (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, ← hu, Units.inv_mul])
  have hdeg₁ : (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀).degree
      = s := by
    refine le_antisymm ?_ (Polynomial.le_degree_of_ne_zero ?_)
    · calc (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀).degree
          ≤ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c))).degree
            + g₀.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (s : WithBot ℕ) := add_le_add Polynomial.degree_C_le hdeg.le
        _ = s := zero_add _
    · rw [Polynomial.coeff_C_mul, ← hu, Units.inv_mul]
      exact one_ne_zero
  have hpoly : f₀ = g₀ * (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) *
      (f₀ /ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀))) +
      f₀ %ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div f₀
      (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀)]
    ring
  have hr₁ : (f₀ %ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) *
      g₀)).degree < s := by
    have h2 := Polynomial.degree_modByMonic_lt f₀ hmonic
    rwa [hdeg₁] at h2
  have hf₁ : Polynomial.toMvRestrictedX0 n c f₀ = Polynomial.toMvRestrictedX0 n c g₀ *
      Polynomial.toMvRestrictedX0 n c
        (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) *
          (f₀ /ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀))) +
      Polynomial.toMvRestrictedX0 n c
        (f₀ %ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀)) := by
    rw [← Polynomial.toMvRestrictedX0_mul, ← Polynomial.toMvRestrictedX0_add]
    exact congrArg _ hpoly
  obtain ⟨Q, -, hQ⟩ := mvWeierstrassDivision_uniqueness_divisible n c hdiv
    (Polynomial.toMvRestrictedX0 n c g₀) s gd (Polynomial.toMvRestrictedX0 n c f₀)
  have key : ∀ (q' : MvPowerSeries.Restricted K c)
      (r' : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))),
      Polynomial.degree r' < s → Polynomial.toMvRestrictedX0 n c f₀ =
        Polynomial.toMvRestrictedX0 n c g₀ * q' + Polynomial.toMvRestrictedX0 n c r' →
      q' = Q := by
    intro q' r' hr' hf'
    refine hQ q' ⟨r', ⟨hr', hf'⟩, ?_⟩
    rintro r'' ⟨-, hf''⟩
    exact Polynomial.toMvRestrictedX0_injective n c (add_left_cancel (hf''.symm.trans hf'))
  refine ⟨Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) *
      (f₀ /ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀)),
    ⟨f₀ %ₘ (Polynomial.C (↑u⁻¹ : MvPowerSeries.Restricted K (Fin.tail c)) * g₀),
      ⟨hr₁, hf₁⟩, ?_⟩, ?_⟩
  · rintro r'' ⟨-, hf''⟩
    exact Polynomial.toMvRestrictedX0_injective n c (add_left_cancel (hf''.symm.trans hf₁))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.toMvRestrictedX0_injective n c
      ((key _ _ hr' hf').trans (key _ _ hr₁ hf₁).symm)

/-- **Multivariate Weierstrass preparation, existence, at divisible-closure radii.** -/
theorem mvWeierstrassPreparation_exists_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s) :
    ∃ (ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)))
      (e : MvPowerSeries.Restricted K c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 n c ω := by
  refine extension_frame n c hdiv ?_
  intro L _ _ _ _ _ hiso hcL
  obtain ⟨ωL, eL, hmL, hdL, hnL, heL, hgL⟩ := mvWeierstrassPreparation_exists n c hcL
    (MvRestricted.mapAlgebra L c hiso g) s (distinguishedMvGen_mapAlgebra n c L hiso gd)
  obtain ⟨ue, hue⟩ := heL
  -- over `L`, dividing `(X 0) ^ s` by `mapAlg g` has quotient `ue⁻¹` and remainder
  -- `X ^ s − ωL`, so descending that division recovers `ωL` (and the unit) over `K`
  have hrdeg : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted L (Fin.tail c))) ^ s
      - ωL).degree < s := by
    have hdd : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted L (Fin.tail c)))
        ^ s).degree = ωL.degree := by
      rw [Polynomial.degree_X_pow, hdL]
    have hlc : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted L (Fin.tail c)))
        ^ s).leadingCoeff = ωL.leadingCoeff := by
      rw [(Polynomial.monic_X_pow (n := s)).leadingCoeff, hmL.leadingCoeff]
    have h := Polynomial.degree_sub_lt hdd (pow_ne_zero s Polynomial.X_ne_zero) hlc
    rwa [Polynomial.degree_X_pow] at h
  have h1 : MvRestricted.mapAlgebra L c hiso g *
      ((ue⁻¹ : (MvPowerSeries.Restricted L c)ˣ) : MvPowerSeries.Restricted L c)
      = Polynomial.toMvRestrictedX0 n c ωL := by
    rw [hgL, ← hue, mul_comm (↑ue : MvPowerSeries.Restricted L c) _, mul_assoc,
      ue.mul_inv, mul_one]
  have hdivE : MvRestricted.mapAlgebra L c hiso (Polynomial.toMvRestrictedX0 n c
      ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s))
      = MvRestricted.mapAlgebra L c hiso g *
        ((ue⁻¹ : (MvPowerSeries.Restricted L c)ˣ) : MvPowerSeries.Restricted L c)
      + Polynomial.toMvRestrictedX0 n c
        ((Polynomial.X : Polynomial (MvPowerSeries.Restricted L (Fin.tail c))) ^ s
          - ωL) := by
    rw [MvRestricted.mapAlgebra_toMvRestrictedX0, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.toMvRestrictedX0_sub, h1]
    ring
  obtain ⟨q₀, r₀, hr₀, heq, hq₀map, hr₀map⟩ :=
    mvWeierstrassDivision_descend n c L hiso g s gd
      (Polynomial.toMvRestrictedX0 n c
        ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s))
      hrdeg hdivE
  have hωmap : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s
      - r₀).map (MvRestricted.mapAlgebra L (Fin.tail c) hiso) = ωL := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hr₀map]
    ring
  have hωmonic : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s
      - r₀).Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one s
      (Polynomial.natDegree_le_iff_degree_le.mpr
        (le_trans (Polynomial.degree_sub_le _ _)
          (max_le (le_of_eq (Polynomial.degree_X_pow s)) hr₀.le))) ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt hr₀, sub_zero]
  have hωdeg : ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s
      - r₀).degree = s := by
    refine le_antisymm (le_trans (Polynomial.degree_sub_le _ _)
      (max_le (le_of_eq (Polynomial.degree_X_pow s)) hr₀.le))
      (Polynomial.le_degree_of_ne_zero ?_)
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt hr₀, sub_zero]
    exact one_ne_zero
  have hωnorm : ‖Polynomial.toMvRestrictedX0 n c
      ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s - r₀)‖
      = (c 0) ^ s := by
    rw [← MvRestricted.norm_mapAlgebra L c hiso, MvRestricted.mapAlgebra_toMvRestrictedX0,
      hωmap]
    exact hnL
  have hq₀unit : IsUnit q₀ := isUnit_of_isUnit_mapAlgebraMv L c hiso
    (by rw [hq₀map]; exact (ue⁻¹).isUnit)
  obtain ⟨uq, huq⟩ := hq₀unit
  refine ⟨(Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s - r₀,
    ((uq⁻¹ : (MvPowerSeries.Restricted K c)ˣ) : MvPowerSeries.Restricted K c),
    hωmonic, hωdeg, hωnorm, (uq⁻¹).isUnit, ?_⟩
  have hfact : Polynomial.toMvRestrictedX0 n c
      ((Polynomial.X : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) ^ s - r₀)
      = g * q₀ := by
    rw [Polynomial.toMvRestrictedX0_sub, heq]
    ring
  rw [hfact, ← huq, mul_comm g, ← mul_assoc, uq.inv_mul, one_mul]

/-- **Multivariate Weierstrass preparation, existence and uniqueness, at divisible-closure
radii.** -/
theorem mvWeierstrassPreparation_unique_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g : MvPowerSeries.Restricted K c) (s : ℕ) (gd : distinguishedMvGen n c g s) :
    ∃! ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! e : MvPowerSeries.Restricted K c, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 n c ω := by
  obtain ⟨ω, e, ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩ :=
    mvWeierstrassPreparation_exists_divisible n c hdiv g s gd
  have hcs : (0 : ℝ) < (c 0) ^ s := pow_pos (StrongPos_pos c 0) s
  refine ⟨ω, ⟨e, ⟨ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, -, hge'⟩
    have hsub : (e' - e) * Polynomial.toMvRestrictedX0 n c ω = 0 := by
      rw [sub_mul, ← hge', ← hg1, sub_self]
    have hn0 : ‖e' - e‖ * ‖Polynomial.toMvRestrictedX0 n c ω‖ = 0 := by
      rw [← norm_mul, hsub, norm_zero]
    rw [ωn] at hn0
    rcases mul_eq_zero.mp hn0 with h' | h'
    · exact sub_eq_zero.mp (norm_eq_zero.mp h')
    · exact absurd h' hcs.ne'
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, ⟨ue', hue'⟩, hg1'⟩, -⟩
    have rd : (ω' - ω).degree < (s : WithBot ℕ) := by
      simpa [ω'd] using Polynomial.degree_sub_lt (ω'd.trans ωd.symm) ω'm.ne_zero
        (by rw [ω'm.leadingCoeff, ωm.leadingCoeff])
    have h0 : (0 : MvPowerSeries.Restricted K c) =
        g * ((↑ue⁻¹ : MvPowerSeries.Restricted K c) - ↑ue'⁻¹) +
          Polynomial.toMvRestrictedX0 n c (ω' - ω) := by
      rw [mul_sub, Polynomial.toMvRestrictedX0_sub]
      have h1 : g * (↑ue⁻¹ : MvPowerSeries.Restricted K c) =
          Polynomial.toMvRestrictedX0 n c ω := by
        rw [hg1, ← hue, mul_comm (↑ue : MvPowerSeries.Restricted K c) _, mul_assoc,
          ue.mul_inv, mul_one]
      have h2 : g * (↑ue'⁻¹ : MvPowerSeries.Restricted K c) =
          Polynomial.toMvRestrictedX0 n c ω' := by
        rw [hg1', ← hue', mul_comm (↑ue' : MvPowerSeries.Restricted K c) _, mul_assoc,
          ue'.mul_inv, mul_one]
      grind
    rw [← sub_eq_zero]
    refine Polynomial.toMvRestrictedX0_injective n c ?_
    rw [Polynomial.toMvRestrictedX0_zero]
    exact norm_le_zero_iff.mp (by simpa [norm_zero] using
      (mvWeierstrassDivision_bounds_r n c g s gd 0 _ _ rd h0))

/-- **Multivariate Weierstrass preparation for `X 0`-polynomials at divisible-closure
radii** — the endpoint a multivariate Newton-polygon theory would consume.  As before,
`IsUnit (Polynomial.toMvRestrictedX0 n c e)` is unit-ness in the restricted ring. -/
theorem mvWeierstrassPreparation_polynomial_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    (g₀ : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))) (s : ℕ)
    (gd : distinguishedMvGen n c (Polynomial.toMvRestrictedX0 n c g₀) s) :
    ∃! ω : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)),
    ∃! e : Polynomial (MvPowerSeries.Restricted K (Fin.tail c)), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n c ω‖ = (c 0) ^ s ∧
      IsUnit (Polynomial.toMvRestrictedX0 n c e) ∧
      Polynomial.toMvRestrictedX0 n c g₀ =
        Polynomial.toMvRestrictedX0 n c e * Polynomial.toMvRestrictedX0 n c ω := by
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg⟩, he_uniq⟩, hω_uniq⟩ :=
    mvWeierstrassPreparation_unique_divisible n c hdiv
      (Polynomial.toMvRestrictedX0 n c g₀) s gd
  have h0 : (0 : Polynomial (MvPowerSeries.Restricted K (Fin.tail c))).degree
      < (s : WithBot ℕ) := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe s
  -- the only new content over uniqueness: the unit `e` is an `X 0`-polynomial, being the
  -- quotient of the division of `g₀` by the distinguished `X 0`-polynomial `ω`
  obtain ⟨e₀, ⟨r₀, ⟨hr₀, hf₀⟩, -⟩, -⟩ := mvWeierstrassDivision_polynomial_divisible n c hdiv
    ω s (distinguishedMvGen_of_monic n c ω s ωm ωd ωn) ωd.le g₀
  have he₀ : e = Polynomial.toMvRestrictedX0 n c e₀ :=
    mvWeierstrassDivision_q_unique n c (Polynomial.toMvRestrictedX0 n c ω) s
      (distinguishedMvGen_of_monic n c ω s ωm ωd ωn) (Polynomial.toMvRestrictedX0 n c g₀) h0
      (by rw [Polynomial.toMvRestrictedX0_zero, add_zero, hg, mul_comm]) hr₀ hf₀
  have hg₀ : Polynomial.toMvRestrictedX0 n c g₀ =
      Polynomial.toMvRestrictedX0 n c e₀ * Polynomial.toMvRestrictedX0 n c ω := he₀ ▸ hg
  refine ⟨ω, ⟨e₀, ⟨ωm, ωd, ωn, he₀ ▸ he, hg₀⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, hu', hg'⟩
    exact Polynomial.toMvRestrictedX0_injective n c
      ((he_uniq _ ⟨ωm, ωd, ωn, hu', hg'⟩).trans he₀)
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, -⟩
    refine hω_uniq ω' ⟨Polynomial.toMvRestrictedX0 n c e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, ?_⟩
    rintro e'' ⟨-, -, -, -, hg''⟩
    exact mvWeierstrassDivision_q_unique n c (Polynomial.toMvRestrictedX0 n c ω') s
      (distinguishedMvGen_of_monic n c ω' s ω'm ω'd ω'n)
      (Polynomial.toMvRestrictedX0 n c g₀) h0
      (by rw [Polynomial.toMvRestrictedX0_zero, add_zero, hg'', mul_comm]) h0
      (by rw [Polynomial.toMvRestrictedX0_zero, add_zero, hg', mul_comm])

end MvDivisible

/-! ## §6  Consistency: the `n = 0` collapse recovers the one-variable theory

At `n = 0` the coefficient Tate algebra has no variables and collapses to the base field
(`foo`/`foo_isom` in `RestrictedIso.lean`), so `MvRestricted K c` at a `Fin 1`-tuple *is* the
one-variable restricted ring at radius `c 0`, and the §4/§5 endpoints must recover the
one-variable theorems of `WPrep_gen.lean`.  This section states that once, as a test:

* `Restricted.congrBase` — base change of a one-variable restricted ring along an isometric
  ring isomorphism (applied below to the collapse `T₀ ≅ K`), with its norm and
  `distinguishedGen` transport;
* the first `example` rederives the statement of `weierstrassDivision_existance_divisible`
  verbatim from `mvWeierstrassDivision_existance_divisible` at `n = 0`, through the composite
  `MvRestricted K c ≃ Restricted T₀ (c 0) ≃ Restricted K (c 0)`;
* the second `example` checks the `c = 1` regime of the original file comment: at the
  constant tuple the value-group hypothesis of the rung-1 endpoints is witnessed by `1`.

Per the module docstring, once this file is stable the one-variable §4–§5 of
`WPrep_gen.lean` could be refactored away as the `n = 0` shadow of this file. -/

section CongrBase

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
  {S' : Type*} [NormedCommRing S'] [IsUltrametricDist S'] (c₀ : ℝ)

omit [IsUltrametricDist S] [IsUltrametricDist S'] in
private lemma isRestricted_map_norm_eq (e : S →+* S') (he : ∀ x, ‖e x‖ = ‖x‖)
    {f : PowerSeries S} (hf : PowerSeries.IsRestricted c₀ f) :
    PowerSeries.IsRestricted c₀ (PowerSeries.map e f) := by
  rw [PowerSeries.isRestricted_iff] at hf ⊢
  exact hf.congr fun k => by rw [PowerSeries.coeff_map, he]

/-- Base change of a one-variable restricted ring along an isometric ring isomorphism of the
coefficients (coefficientwise `e`; the collapse `T₀ ≅ K` at `n = 0` is the instance used
below). -/
noncomputable def Restricted.congrBase (e : S ≃+* S') (he : ∀ x, ‖e x‖ = ‖x‖) :
    PowerSeries.Restricted S c₀ ≃+* PowerSeries.Restricted S' c₀ where
  toFun f := ⟨PowerSeries.map (e : S →+* S') f.1, isRestricted_map_norm_eq c₀ _ he f.2⟩
  invFun g := ⟨PowerSeries.map (e.symm : S' →+* S) g.1, isRestricted_map_norm_eq c₀ _
    (fun x => by
      have h := he (e.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) g.2⟩
  left_inv f := Subtype.ext (PowerSeries.ext fun k => by
    show PowerSeries.coeff k (PowerSeries.map (e.symm : S' →+* S)
      (PowerSeries.map (e : S →+* S') f.1)) = PowerSeries.coeff k f.1
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _)
  right_inv g := Subtype.ext (PowerSeries.ext fun k => by
    show PowerSeries.coeff k (PowerSeries.map (e : S →+* S')
      (PowerSeries.map (e.symm : S' →+* S) g.1)) = PowerSeries.coeff k g.1
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.apply_symm_apply _)
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.map (e : S →+* S')) f.1 g.1)
  map_add' f g := Subtype.ext (map_add (PowerSeries.map (e : S →+* S')) f.1 g.1)

lemma Restricted.norm_congrBase [StrongPos (fun _ : Unit ↦ c₀)] (e : S ≃+* S')
    (he : ∀ x, ‖e x‖ = ‖x‖) (f : PowerSeries.Restricted S c₀) :
    ‖Restricted.congrBase c₀ e he f‖ = ‖f‖ := by
  show PowerSeries.gaussNorm norm c₀ (PowerSeries.map (e : S →+* S') f.1) =
    PowerSeries.gaussNorm norm c₀ f.1
  rw [PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  exact iSup_congr fun k => by
    rw [PowerSeries.coeff_map]
    exact congrArg (· * c₀ ^ k) (he (PowerSeries.coeff k f.1))

lemma Restricted.congrBase_toRestricted (e : S ≃+* S') (he : ∀ x, ‖e x‖ = ‖x‖)
    (p : Polynomial S) :
    Restricted.congrBase c₀ e he (Polynomial.toRestricted c₀ p) =
      Polynomial.toRestricted c₀ (p.map (e : S →+* S')) :=
  Subtype.ext (PowerSeries.ext fun k => by
    show PowerSeries.coeff k (PowerSeries.map (e : S →+* S') (p : PowerSeries S)) =
      PowerSeries.coeff k ((p.map (e : S →+* S') : Polynomial S') : PowerSeries S')
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_map])

lemma distinguishedGen_congrBase [StrongPos (fun _ : Unit ↦ c₀)] (e : S ≃+* S')
    (he : ∀ x, ‖e x‖ = ‖x‖) {f : PowerSeries.Restricted S c₀} {s : ℕ}
    (hf : distinguishedGen norm c₀ f.1 s) :
    distinguishedGen norm c₀ (Restricted.congrBase c₀ e he f).1 s := by
  obtain ⟨h1, h2, h3⟩ := hf
  have hcoeff : ∀ k, PowerSeries.coeff k (Restricted.congrBase c₀ e he f).1 =
      e (PowerSeries.coeff k f.1) := fun k => rfl
  have hgauss : PowerSeries.gaussNorm norm c₀ (Restricted.congrBase c₀ e he f).1 =
      PowerSeries.gaussNorm norm c₀ f.1 :=
    calc PowerSeries.gaussNorm norm c₀ (Restricted.congrBase c₀ e he f).1
        = ‖Restricted.congrBase c₀ e he f‖ := (Restricted.norm_eq c₀ _).symm
      _ = ‖f‖ := Restricted.norm_congrBase c₀ e he f
      _ = PowerSeries.gaussNorm norm c₀ f.1 := Restricted.norm_eq c₀ f
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoeff]
    exact h1.map (e : S →+* S')
  · rw [hgauss, hcoeff, he]
    exact h2
  · intro t ht
    rw [hcoeff, hcoeff, he, he]
    exact h3 t ht

end CongrBase

section ZeroCollapse

/-- **Consistency test (`n = 0`)**: the multivariate divisible-radius division endpoint
recovers the statement of `weierstrassDivision_existance_divisible` verbatim, through the
collapse `MvRestricted K (fun _ : Fin 1 ↦ c₀) ≃ Restricted T₀ c₀ ≃ Restricted K c₀`. -/
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {c₀ : ℝ} [StrongPos (fun _ : Unit ↦ c₀)] (hdiv : MemDivisibleValueGroup K c₀)
    (g : PowerSeries.Restricted K c₀) (s : ℕ)
    (gd : distinguishedGen norm c₀ g.1 s) (f : PowerSeries.Restricted K c₀) :
    ∃ (q : PowerSeries.Restricted K c₀) (r : Polynomial K),
      Polynomial.degree r < s ∧ f = g * q + Polynomial.toRestricted c₀ r := by
  haveI : StrongPos (fun _ : Fin 1 => c₀) := ⟨fun _ => StrongPos_pos (fun _ : Unit ↦ c₀) ()⟩
  -- the collapse of the empty coefficient algebra is an isometry
  have hfoo : ∀ x : MvPowerSeries.Restricted K (Fin.tail (fun _ : Fin 1 => c₀)),
      ‖foo K (Fin.tail (fun _ : Fin 1 => c₀)) x‖ = ‖x‖ := fun x => by
    have h := (foo_isom (R := K) (Fin.tail (fun _ : Fin 1 => c₀))).dist_eq x 0
    rwa [show foo_isom (R := K) (Fin.tail (fun _ : Fin 1 => c₀)) 0 = 0 from
      map_zero (foo K (Fin.tail (fun _ : Fin 1 => c₀))), dist_zero_right,
      dist_zero_right] at h
  -- pull `g` back through the collapse; distinguishedness transports
  have gdMv : distinguishedMvGen 0 (fun _ : Fin 1 => c₀)
      ((MvRestricted.finSuccEquiv K 0 (fun _ : Fin 1 => c₀)).symm
        ((Restricted.congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))) hfoo).symm g))
      s := by
    refine (distinguishedMvGen_finSuccEquiv_symm 0 (fun _ : Fin 1 => c₀) _ s).mpr ?_
    exact distinguishedGen_congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))).symm
      (fun x => by
        have h := hfoo ((foo K (Fin.tail (fun _ : Fin 1 => c₀))).symm x)
        rw [RingEquiv.apply_symm_apply] at h
        exact h.symm) gd
  -- divide in the multivariate ring
  obtain ⟨qMv, rMv, hrMv, hfMv⟩ := mvWeierstrassDivision_existance_divisible 0
    (fun _ : Fin 1 => c₀) (fun _ => hdiv)
    ((MvRestricted.finSuccEquiv K 0 (fun _ : Fin 1 => c₀)).symm
      ((Restricted.congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))) hfoo).symm g))
    s gdMv
    ((MvRestricted.finSuccEquiv K 0 (fun _ : Fin 1 => c₀)).symm
      ((Restricted.congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))) hfoo).symm f))
  -- push the division forward through the collapse
  refine ⟨Restricted.congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))) hfoo
      (MvRestricted.finSuccEquiv K 0 (fun _ : Fin 1 => c₀) qMv),
    rMv.map ((foo K (Fin.tail (fun _ : Fin 1 => c₀))) :
      MvPowerSeries.Restricted K (Fin.tail (fun _ : Fin 1 => c₀)) →+* K),
    lt_of_le_of_lt Polynomial.degree_map_le hrMv, ?_⟩
  have h1 := congrArg (MvRestricted.finSuccEquiv K 0 (fun _ : Fin 1 => c₀)) hfMv
  rw [RingEquiv.apply_symm_apply, map_add, map_mul, RingEquiv.apply_symm_apply,
    MvRestricted.finSuccEquiv_toMvRestrictedX0] at h1
  have h2 := congrArg
    (Restricted.congrBase c₀ (foo K (Fin.tail (fun _ : Fin 1 => c₀))) hfoo) h1
  rwa [RingEquiv.apply_symm_apply, map_add, map_mul, RingEquiv.apply_symm_apply,
    Restricted.congrBase_toRestricted] at h2

/-- Instantiation check for the `c = 1` regime: at the constant tuple the value-group
hypothesis of the rung-1 endpoints is witnessed by `1` throughout. -/
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) (hone : StrongPos (fun _ : Fin (n + 1) => (1 : ℝ)))
    (g : MvPowerSeries.Restricted K (fun _ : Fin (n + 1) => (1 : ℝ))) (s : ℕ)
    (gd : distinguishedMvGen n (fun _ : Fin (n + 1) => (1 : ℝ)) g s) :
    ∃ (ω : Polynomial (MvPowerSeries.Restricted K
        (Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)))))
      (e : MvPowerSeries.Restricted K (fun _ : Fin (n + 1) => (1 : ℝ))), ω.Monic ∧
      ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 n (fun _ : Fin (n + 1) => (1 : ℝ)) ω‖ = (1 : ℝ) ^ s ∧
      IsUnit e ∧ g = e * Polynomial.toMvRestrictedX0 n (fun _ : Fin (n + 1) => (1 : ℝ)) ω :=
  mvWeierstrassPreparation_exists n (fun _ : Fin (n + 1) => (1 : ℝ))
    (fun _ => ⟨1, by simp⟩) g s gd

end ZeroCollapse
