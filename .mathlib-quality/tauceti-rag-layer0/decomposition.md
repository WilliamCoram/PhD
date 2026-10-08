# Decomposition: rigid analytic geometry, Layer 0 (the Tate algebras)

Companion to `plan.md`. Every leaf below is a declaration of the skeleton, stated with `sorry`; the
pointer is `File.lean · declaration name` (names are stable, line numbers are not; the script
`scratch/sorries.py` prints the current line of every open declaration). Sources:

- **[RM]** the roadmap `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0, cited by clause
  (§0.1.1 … §0.4.3);
- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis* (1984). The PDF is an image scan, so
  every quoted passage was transcribed by hand into `references/bgr-*.md`; a locator
  `bgr-5.1.md:118` is a line of that transcription, and the transcription records the book page;
- **[Bo]** Bosch, *Lectures on Formal and Rigid Geometry* (2008 preprint), text layer in
  `references/bosch-lectures.txt`; a locator is a line of that file. Quotes from it normalise the
  ligatures and the broken spacing of the PDF extraction (`ﬁ` → `fi`, `f∈Tn` → `f ∈ Tₙ`) and nothing
  else;
- **[SEAM]** the restricted-power-series floor `PhD/TauCeti/Code/RigidAnalyticGeometry/Restricted/**`
  (21 files, sorry-free, ported from the user's mathlib4#42867 development; plan §"The floor");
- **[TOWER]** `TateAlgebra/Tower.lean` (sorry-free): the floor restated at the unit polyradius;
- **[PFA]** the chain's `PhD/TauCeti/Code/PadicFunctionalAnalysis/{UnitBall, PowerBounded, Sums}.lean`
  (sorry-free).

Discharge lines name the lemmas a worker will call. Every Mathlib name was checked by elaboration
against the pin: `scratch/names_mathlib{1,…,5}.lean`, and `scratch/names_tickets_mathlib.lean`, which
is generated from the tickets' own "Mathlib lemmas needed" blocks (443 names) — no error and no
deprecation warning. Every floor, chain and board name was checked by `scratch/names_chain.lean` and
`scratch/names_tickets_chain.lean` (53 names, 0 errors). Names that turned out not to exist, or to
be deprecated, are recorded where they occur. Attack categories: **[1]** counterexample search, **[2]** edge cases, **[3]**
hypothesis strength, **[4]** source drift, **[5]** discharge, **[6]** composition (internal nodes).

## Skeleton location

`PhD/TauCeti/Code/RigidAnalyticGeometry/` — `TateAlgebra/{Basic, Reduction, Eval, EvalReduction,
MaxModulus, Distinguished, Finiteness, Chart, Rueckert, StrictlyClosed, Stable, Examples}.lean`,
`{SupSeminorm, Rueckert, Bald, OrthonormalLift, WeaklyStable, Japanese}.lean`, and
`PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean` (the slice of the `p`-adic functional
analysis roadmap's §2.2 that this layer consumes). 19 files, 205 open declarations, 215 `sorry`s
(three definitions carry several `sorry` fields); `TateAlgebra/Tower.lean` and the floor are complete.

Gate: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples` (the leaf imports the
whole board) — `Build completed successfully (2722 jobs)`, `sorry` warnings only, verified 2026-10-02
after the last statement change. Elaborated signatures of all declarations: `scratch/signatures.txt`.

## Prior-B2 consultation (Step 4.6), once for the whole tree

All B2 logs under `.mathlib-quality/` were read: the default log (8 entries) and the board logs
`jacobs` (4), `lwx-conductor` (5), `lwx-h1` (2), `lwx-halo` (3), `lwx-seam-m` (2), `lwx-theta` (6),
`tauceti-of-layer0` (2). **No leaf matches by name.** The defect *shapes* recorded there were applied
to every leaf as edge-case attacks:

| Prior defect shape | Log entry | Where it was tested here | Outcome |
|---|---|---|---|
| instance-implicit section variable silently dropped from the elaborated statement | `lwx-h1` W5, `lwx-conductor` R13–R17, `tauceti-of-layer0` T023 | every declaration, by reading `scratch/signatures.txt` | **two hits**, fixed: the three Tate-algebra instances had lost `[CompleteSpace K]`; `IsFractionRing.normAbsoluteValue` had lost `[NormMulClass A] [Nontrivial A]` (defects D5, D6 below). `instNontrivial`, `instCharZero`, `instIsDomain` carry no `Fact (∀ i, 0 < c i)` and are true without it (L1.3–L1.5) |
| statement generalised beyond the source's hypotheses (characteristic `p`, radius `> 1`) | default log C3 | every leaf more general than its source: L1.* (general polyradius, normed ring), L3.* (contractive `φ`), L6.3 (finite `S`, any `L`), L10.* (abstract Rückert), L14.* (no completeness), L16.* (no nontriviality) | each generalisation re-derived by hand; **one hit**, fixed: `IsOrthonormalBasis.exists_hasSum` is false over a non-complete field (D7) |
| normalisation silently assumed (`‖p‖ = 1/p`) | `lwx-seam-m` X-4 | L6.2 (`‖(m : K)‖ = 1` is a hypothesis, produced by L6.1 for every ultrametric field), L19.* (`ℚ_[p]`, `Padic.norm_p` is a theorem) | clean |
| unconstrained parameter | `lwx-theta` T-AG1a, `jacobs` J015 | L9.6 (exponents `e i`): **one hit**, fixed (D1); L16.1 (`N : V → ℝ` arbitrary — proved to need nothing) | fixed / clean |
| junk values (`iSup` of an unbounded family, `natDegree 0`, `spectralValue 0`, `infDist` to `∅`) | `jacobs` W001–W003, default log T002 | L5.1–L5.8 (`evalNorm` at a non-algebraic residue class is `0`; `supSeminorm` on the zero ring is `0`), L7.16 (`natDegree 0`), L15.17 (`infDist`, `N` nonempty) | clean; each junk case is stated in the leaf |
| statement not instantiable by its consumer | `lwx-h1` W/I15 | the four milestone assemblies were compiled against the skeleton (`scratch/spot3.lean`, `spot4.lean`, `spot5.lean`) | clean |
| polynomial versus power-series range of an index | `lwx-theta` S7.10 | L7.15–L7.16 (`natDegree`, `leadingCoeff` of the reduction), L9.5–L9.7 | clean |
| definition of a topology differs from the expected one | `tauceti-of-layer0` T039 | L2.14–L2.15 use the chain's `PowerBounded.IsPowerBounded` and Mathlib's `IsTopologicallyNilpotent` with the norm topology only | clean |

## Statement defects found by the adversarial pass (all repaired in the skeleton)

| # | Declaration | Defect | Repair |
|---|---|---|---|
| D1 | `MvPolynomial.leadingCoeff_finSuccEquiv_shear_monomial` | false for an exponent `e i = 0`: the factor `X (i+1) + 1` has leading coefficient `X (i+1) + 1`, not `1` | hypothesis `he : ∀ i, 0 < e i` |
| D2 | `exists_eq_sum_smul_of_hasSum` | false for `C < 0` with an empty index set (`a = 0`, but `‖q j‖ ≤ C` is impossible) | hypothesis `hC0 : 0 ≤ C` |
| D3 | `IsWeierstrassPolynomial.eq_of_mul_eq_mul` | the degree comparison goes through the reduction, which needs units detected by the reduction | `[CompleteSpace K]` |
| D4 | `IsOrthonormalBasis.of_residue_basis` | carried `[CompleteSpace V]`, never used | hypothesis removed (the statement is stronger) |
| D5 | `instIsNoetherianRing`, `instUniqueFactorizationMonoid`, `instIsJacobsonRing` on `TateAlgebra K n` | section variable `[CompleteSpace K]` dropped by elaboration: as elaborated they claimed the three properties over a non-complete field, where Weierstrass division is unavailable | explicit binders |
| D6 | `IsFractionRing.normAbsoluteValue` | section variables `[NormMulClass A] [Nontrivial A]` dropped: multiplicativity is false without `NormMulClass` | explicit binders |
| D7 | `IsOrthonormalBasis.exists_hasSum` | **false over a non-complete field**: `ℚ_[p]` is a complete normed space over `ℚ` with the `p`-adic norm, `{1}` is an orthonormal family with dense span, and no `x ∈ ℚ_[p] ∖ ℚ` is `a • 1` | `[CompleteSpace K]` (found 2026-10-01 while writing L13.9's proof) |
| D8 | `IsWeierstrassPolynomial.of_mul` | bundled conclusion `P ∧ Q` (statement-shape rule) | split into `of_mul_left`, `of_mul_right`; `of_mul` is the one-line assembly |
| D9 | `instCharZero` | first stated for `FractionRing`; Mathlib has `IsFractionRing.charZero`, so the missing instance is the one on `Restricted R c` | moved |
| D10 | `isWeaklyStable_fractionRing`, `Examples.not_isMulDistinguishedX0_X_one` | carried `[CompleteSpace K]`, never used (over-specified) | hypothesis omitted |

## Statement-shape check (gate condition 7)

`scratch/sorries.json` was scanned for `∧` in conclusions. After D8 no open declaration has a
top-level conjunction. The remaining conjunctions are of two kinds, both allowed:

- **characterisations** `P ↔ Q₁ ∧ Q₂`: `isUnit_iff_norm_coeff_lt`, `isMulDistinguishedX0_iff_reduction`,
  `isWeierstrassPolynomial_iff`, `mem_unitLocalization_iff` (each is one criterion, used as a rewrite);
- **shared-witness existentials** `∃ w, P w ∧ Q w`, where the parts are about the same witness and
  cannot be stated separately: `exists_norm_smul_eq_one`, `exists_norm_eq_one_not_isUnit_C_add`,
  `exists_lt_natCast_norm_eq_one`, `exists_finset_splittingField_X_pow_sub_one`,
  `exists_norm_aeval_eq_norm`, `exists_evalNorm_eq_norm`, `exists_evalNorm_eq_norm_and_notMem`,
  `exists_isWeierstrassPolynomial_of_isMulDistinguishedX0`, `existsUnique_remainder`,
  `exists_ringEquiv_mem_map`, `IsBRing.exists_monic_norm_aeval_lt_one`,
  `exists_norm_sub_le_of_span_residue`, `MvPolynomial.exists_basis_adaptedFamily`,
  `exists_generators_reductionSubmodule`, `exists_isBald_forall_coeff_mem`,
  `exists_eq_sum_smul_of_hasSum`, `exists_isOrthonormalBasis_adaptedFamily`,
  `exists_generators_forall_exists_isNearest`, `exists_generators_norm_le`,
  `exists_generators_norm_le_ideal`.

Multi-part source statements are split: BGR 5.2.1/2 into existence and two uniqueness statements,
BGR 5.2.3/3 (i), (ii) into `existsUnique_remainder` and `bijective_quotientMap`, BGR 5.1.3/1's two
sentences into `isUnit_iff_norm_coeff_lt` and `isUnit_coe_iff_isUnit_reduction`, Bosch 1.3/5 (ii),
(iii) into `exists_hasSum`, `norm_coeff_le_of_hasSum`, `norm_le_of_hasSum`, `eq_of_hasSum`.

---

## G1 — The Tate algebra as a Banach algebra (`TateAlgebra/Basic.lean`), [RM] §0.1.1

### Source and prose proof

[BGR] 5.1.1 (`bgr-5.1.md:27–41`): *"For `f = Σ_ν a_ν X^ν ∈ Tₙ`, the real number `|f| := max_ν |a_ν|`
is well-defined. … **Proposition 1.** `Tₙ(k)` is a `k`-subalgebra of the algebra of formal power
series `k⟦X₁, …, Xₙ⟧`. The Gauss norm is a `k`-algebra norm on `Tₙ(k)` making it into a `k`-Banach
algebra containing the polynomial algebra `k[X₁, …, Xₙ]` as a dense `k`-subalgebra. Using the fact
that `|Tₙ| = |k|`, we see that every non-zero series can be normed to length 1 by multiplication
with a scalar from `k`: **Observation 2.** For every `f ∈ Tₙ − {0}`, there exists `c ∈ k` such that
`|cf| = 1`."* [BGR] 5.1.2/1 (`bgr-5.1.md:67`, `:84`): *"The Gauss norm is a valuation on `Tₙ`. … In
particular, the residue algebra `Tₙ~` is an integral domain."*

The floor [SEAM] already has the Gauss norm as a `NormedRing` structure, complete when the
coefficient ring is, multiplicative when the coefficient norm is (`NormMulClass`), with
`norm_le_iff`, `norm_lt_iff` (the norm is the supremum of the Gauss terms, and it is attained) and
`hasSum_monomial` (a series is the sum of its monomials). What BGR 5.1.1 states beyond that is read
off these: each Gauss term is bounded by the norm and one of them equals it; the truncations
converge, so polynomials are dense; a scalar `a ∈ K` scales the norm by `‖a‖`, so the norm is a
`K`-algebra norm; the constants embed, so nontriviality and characteristic zero pass up, and a
multiplicative norm has no zero divisors. At the unit polyradius every Gauss term is the norm of a
coefficient, which gives `|f| = max |a_ν| ∈ |K|`, the coefficientwise criteria, the finiteness of the
set of large coefficients (the series is restricted), and the normalisation of Observation 2.

### Leaves

- **L1.1** `norm_coeff_mul_prod_le` (`Basic.lean`) — Q: [BGR] `bgr-5.1.md:29` *"`|f| := max_ν |a_ν|`"*
  (each term is at most the maximum), at a general polyradius. M: the Lean statement is the bound
  `‖a_t‖ · c^t ≤ ‖f‖`; for `c = 1` it is the quoted inequality. D: [SEAM] `(norm_le_iff c f).mp le_rfl t`
  (one lemma). A: [2] `f = 0`: `0 ≤ 0` ✓; `t = 0`: `‖a₀‖ ≤ ‖f‖` ✓. [3] needs `Fact (∀ i, 0 < c i)`
  only through the norm instance; no hypothesis to drop. [5] `norm_le_iff` is the floor's
  `‖f‖ ≤ ε ↔ ∀ t, ‖coeff t f.1‖ * t.prod (c · ^ ·) ≤ ε`, checked in `names_chain.lean`. SURVIVED.
- **L1.2** `exists_norm_eq_norm_coeff_mul_prod` — Q: [BGR] `bgr-5.1.md:27–31` *"the real number
  `|f| := max_ν |a_ν|` is well-defined"* (the maximum is attained). M: literal, with the Gauss term in
  place of `|a_ν|`. D: [SEAM] `exists_achievesGaussNorm c f` with `norm_def` (the proof of the floor's
  `exists_coeff_ne_zero_norm_eq` without its `f ≠ 0`). A: [2] `f = 0`: any `t` works, `0 = 0 * _` ✓;
  `σ` empty: `t = 0` ✓. [3] no `f ≠ 0` needed — the floor lemma that carries it also returns
  `coeff ≠ 0`, which is not claimed here. [5] two lemmas. SURVIVED.
- **L1.3** `instNontrivial` — Q: [RM] §0.1.4 *"Prove that `Tₙ` is an integral domain (from
  multiplicativity)"* (nontriviality is the first half of `IsDomain`); [BGR] `bgr-5.1.md:35`
  *"containing the polynomial algebra"*. M: for a nontrivial coefficient ring. D: `0 ≠ 1` because the
  constant coefficients differ: `congrArg (fun f ↦ MvPowerSeries.constantCoeff f.1)`, `val_zero`,
  `val_one`. A: [2] `σ` empty: the ring is `R` ✓. [3] the elaborated statement has **no** `Fact`
  hypothesis on `c` (checked in `signatures.txt`); the proof above does not use the norm, so the
  statement is true as elaborated ✓. [5] `MvPowerSeries.constantCoeff_C` and the `val_*` lemmas
  verified. SURVIVED.
- **L1.4** `instCharZero` — Q: [BGR] `bgr-5.3.1.md:40` *"All valued fields of characteristic 0 are
  weakly stable"* (the consumer, §0.4, needs characteristic zero of `Tₙ` to pass to `Q(Tₙ)`). M: glue
  for L18.1–L18.2: `CharZero R → CharZero (Restricted R c)`. D: `charZero_of_injective_ringHom` applied
  to `C c`, injective by the constant coefficient (`val_C`, `MvPowerSeries.constantCoeff_C`). A: [2]
  as L1.3, no `Fact` needed ✓. [3] ⚠ `RingHom.charZero` goes the wrong way (from the codomain);
  the right lemma is `charZero_of_injective_ringHom` (verified, `names_mathlib4.lean`). [5] Mathlib
  supplies `IsFractionRing.charZero`, so this is the only missing instance (defect D9). SURVIVED.
- **L1.5** `instIsDomain` — Q: [BGR] 5.1.2/1 `bgr-5.1.md:67` *"The Gauss norm is a valuation on
  `Tₙ`"*; [Bo] `bosch-lectures.txt:376` *"In particular, it follows that `Tₙ` is an integral domain."*
  M: stated at every polyradius for a coefficient ring with multiplicative norm. D: the elaborated
  statement has no `Fact` hypothesis, so the norm route is unavailable; instead
  `NormMulClass.toNoZeroDivisors` on `R`, the Mathlib instance `NoZeroDivisors (MvPowerSeries σ R)`
  (checked by `inferInstance` for `[Ring R] [NoZeroDivisors R]`, `names_mathlib4.lean`), `val_mul`, and
  `NoZeroDivisors.to_isDomain` with L1.3. A: [1] a zero divisor in `Restricted R c` would be one in
  `MvPowerSeries σ R` ✓ none. [2] `c` with negative entries: still a subring of a domain ✓. [3]
  `Nontrivial R` is necessary (the zero ring is not a domain); `NormMulClass` could be weakened to
  `NoZeroDivisors R`, but the consumers have a normed field and the floor's `NormMulClass` instance is
  the companion statement. [4] the source proves it from the valuation; the Lean route is shorter and
  gives the same statement. SURVIVED.
- **L1.6** `exists_finset_norm_sub_sum_monomial_lt` — Q: [BGR] `bgr-5.1.md:35–36` *"containing the
  polynomial algebra `k[X₁, …, Xₙ]` as a dense `k`-subalgebra"*. M: the quantitative form: the finite
  truncations of `f` approximate `f`. D: [SEAM] `hasSum_monomial c f`, unfolded with
  `Metric.tendsto_atTop` exactly as in the floor's own proof. A: [2] `f = 0`: `s = ∅`, `‖0‖ < ε` ✓.
  [3] `0 < ε` necessary. [5] one floor lemma and one unfolding. SURVIVED.
- **L1.7** `denseRange_toRestricted` — Q: as L1.6 ([BGR] 5.1.1/1). M: literal, for a commutative
  coefficient ring (`MvPolynomial` needs commutativity). D: `Metric.denseRange_iff`, L1.6, and
  `map_sum` with [SEAM] `MvPolynomial.toRestricted_monomial` to write the truncation as the image of
  a polynomial. A: [2] `σ` empty ✓ (every series is a constant). [3] no completeness needed. [5]
  `Metric.denseRange_iff` verified. SURVIVED.
- **L1.8** `norm_smul_eq` — Q: [Bo] `bosch-lectures.txt:373` *"`|cf| = |c||f|`"* (the second property
  of the Gauss norm). M: literal for a normed field `K`. D: `≤` by [SEAM] `norm_le_iff` and L1.1
  (`coeff_smul`, `norm_mul`, `mul_assoc`); `≥` for `a ≠ 0` by applying `≤` to `a⁻¹ • (a • f)`; `a = 0`
  is `zero_smul`. A: [2] `a = 0` ✓, `f = 0` ✓. [3] a field is used only for `a⁻¹`; over a normed ring
  only `≤` holds, which is why the equality is stated for fields. [5] `MvPowerSeries.coeff_smul`,
  `Restricted.val_smul` verified. The instance `instNormedAlgebra` is complete in the skeleton and
  consumes this leaf. SURVIVED.
- **L1.9** `norm_coeff_le` — Q: [BGR] `bgr-5.1.md:29`. M: L1.1 at `c = 1`. D: L1.1 and
  `t.prod ((1 : σ → ℝ) · ^ ·) = 1` (`Finsupp.prod`, `one_pow`, `Finset.prod_const_one`). A: [2] `t = 0`
  ✓. [3] none. [5] the product identity is a `simp` goal. SURVIVED.
- **L1.10** `exists_norm_coeff_eq` — Q: [BGR] `bgr-5.1.md:29` *"`|f| := max_ν |a_ν|`"*. M: literal: the
  maximum is the norm of a coefficient. D: L1.2 and the product identity. A: [2] `f = 0` ✓. [3] no
  `f ≠ 0`. SURVIVED.
- **L1.11** `norm_le_iff_forall_norm_coeff_le` and **L1.12** `norm_lt_iff_forall_norm_coeff_lt` — Q:
  [RM] §0.1.2 *"(coefficientwise criteria)"*; [BGR] `bgr-5.1.md:74–75` *"`Tₙ° := {f ∈ Tₙ ; |f| ≤ 1}`,
  `Tₙˇ := {f ∈ Tₙ ; |f| < 1}`"*. M: the criteria `‖f‖ ≤ ε ↔ ∀ t, ‖a_t‖ ≤ ε` and its strict form. D:
  [SEAM] `norm_le_iff`, `norm_lt_iff` and the product identity. A: [2] `ε < 0`: both sides are
  false, because `0 ≤ ‖a_t‖` at the index `t = 0` (the index type `σ →₀ ℕ` is never empty) ✓. [3] the strict form needs attainment, which the floor's `norm_lt_iff`
  already uses. [5] one floor lemma each. SURVIVED.
- **L1.13** `tendsto_norm_coeff_cofinite` — Q: [BGR] `bgr-5.1.md:18–19` *"`a_{ν₁…νₙ} ∈ k` and
  `|a_{ν₁…νₙ}| → 0` for `ν₁ + ⋯ + νₙ → ∞`"*. M: the cofinite filter on `σ →₀ ℕ` is the Lean form of
  `|ν| → ∞`. D: `f.2` (the defining property `IsRestricted 1 f.1`) rewritten by the product identity.
  A: [2] `σ` infinite: cofinite nullity is the definition, still true ✓. [3] none. [5] the floor uses
  `f.2` in the same way in `hasSum_monomial`. SURVIVED.
- **L1.14** `finite_setOf_le_norm_coeff` — Q: as L1.13. M: for `ε > 0` only finitely many coefficients
  have norm `≥ ε`. D: L1.13, `Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`,
  `not_lt`. A: [2] `ε ≤ 0` would make the set everything — `0 < ε` necessary ✓. [5] three verified
  lemmas. SURVIVED.
- **L1.15** `norm_mem_range_norm` — Q: [BGR] `bgr-5.1.md:38` *"Using the fact that `|Tₙ| = |k|`"*. M:
  `‖f‖ ∈ range norm`; the other inclusion is `norm_C`. D: L1.10. A: [2] `f = 0`: `‖0‖ = ‖(0 : R)‖` ✓.
  [3] holds over any normed ring. SURVIVED.
- **L1.16** `exists_norm_smul_eq_one` — Q: [BGR] 5.1.1/2 `bgr-5.1.md:41` *"For every `f ∈ Tₙ − {0}`,
  there exists `c ∈ k` such that `|cf| = 1`."* M: literal, with `a ≠ 0` recorded (it is used when the
  scaling is undone). D: L1.10 gives `t` with `‖a_t‖ = ‖f‖ ≠ 0`; take `a = a_t⁻¹`; L1.8, `norm_inv`,
  `inv_mul_cancel₀`. A: [1] `f ≠ 0` necessary ✓. [2] `σ` empty: `f` a nonzero constant ✓. [3] no
  nontriviality of the valuation needed, unlike the general Banach-algebra statement — this is
  exactly `|Tₙ| = |K|`. [5] three lemmas. SURVIVED.

### Internal node

- **N1** `instNormedAlgebra` (complete in the skeleton: `norm_smul_le := (norm_smul_eq c a f).le`) —
  source [BGR] 5.1.1/1. [6] children true, parent false? The parent is a one-field structure whose
  field is L1.8 ✓; the `Algebra K (Restricted K c)` instance is the floor's (`Restricted/Algebra.lean`,
  the instance of mathlib4#42867), so there is no second algebra structure to disagree with. [2]
  `K` trivially normed ✓. [5] built by the gate. SURVIVED.

---

## G2 — The reduction (`TateAlgebra/Reduction.lean`), [RM] §0.1.2

### Source and prose proof

[BGR] 5.1.2 (`bgr-5.1.md:78–87`): *"We can extend the canonical epimorphism `~ : k̊ → k̃` … to a map
`~ : Tₙ° → k̃[X]` by setting `(Σ a_ν X^ν)~ := Σ ã_ν X^ν ∈ k̃[X]`. Obviously the kernel of this map is
`Tₙˇ`, and the map is surjective. Therefore we get `Tₙ~ = k̃[X]`. … But then we must have
`T̊ₙ = Tₙ°`, `Ťₙ = Tₙˇ`, and hence `T̃ₙ = Tₙ~ = k̃[X]`."* [Bo] (`bosch-lectures.txt:382–391`): *"the
epimorphism `R → k` extends to an epimorphism `π : R⟨ζ₁, …, ζₙ⟩ → k[ζ₁, …, ζₙ]`,
`Σ c_ν ζ^ν ↦ Σ c̃_ν ζ^ν`. For an element `f ∈ R⟨ζ₁, …, ζₙ⟩` we will call `f̃ = π(f)` the reduction of
`f`. Note that `f̃ = 0` if and only if `|f| < 1`."* [BGR] 5.1.3/1–3 (`bgr-5.1.md:96–97`, `:108–124`):
*"A series `f ∈ Tₙ` with `|f| = 1` is a unit in `Tₙ` if and only if `|f(0)| = 1` and
`|f − f(0)| < 1`. Thus `f` is a unit if and only if `f̃` is a unit (i.e., a constant) in `T̃ₙ`. …
**Lemma 2.** For each `f ∈ Tₙ` with `|f| = 1`, there is an element `c ∈ k` with `|c| = 1` such that
`c + f` is not a unit in `Tₙ`. … **Proposition 3.** `⋂_{𝔪 ∈ Max Tₙ} 𝔪 = (0)`."*

The unit ball `T⁰` is [PFA] `Subring.unitClosedBall`, the ideal `T⁰⁰` is [PFA]
`NormedRing.openUnitBallIdeal`, and the residue field is `IsLocalRing.ResidueField` of the unit ball
of `K`, whose maximal ideal is the open unit ball ([PFA] `maximalIdeal_unitClosedBall`). A series of
`T⁰` has coefficients in `K⁰` (G1), all but finitely many of them in `K⁰⁰` (L1.14 with `ε = 1`), so
reducing each coefficient gives a polynomial. The map is additive and unital coefficientwise, and
multiplicative because a coefficient of a product is a *finite* Cauchy sum, which the residue map
preserves. A coefficient reduces to zero exactly when its norm is `< 1`, so the kernel is `T⁰⁰`
(L1.12). Surjectivity: lift each coefficient of a polynomial; more precisely every `f ∈ T⁰` is a
polynomial over `K⁰` modulo `T⁰⁰`, which is also what the later comparison theorems (G4) use. The
norm criteria for power-bounded and topologically nilpotent elements are [PFA] for any multiplicative
norm. Units: the floor's criterion ([SEAM] `isUnit_iff`, proved from the Neumann series as in Bosch's
Corollary 4) says that the constant coefficient dominates; in `T⁰` a unit is detected modulo `T⁰⁰`
([PFA] `isUnit_iff_isUnit_mk`); for a series of norm one, being a unit of `T` and of `T⁰` agree
because the inverse also has norm one. Lemma 2 is the two-case argument of BGR; Proposition 3 follows
with `Ideal.mem_jacobson_bot`.

### Leaves

- **L2.1** `finite_support_residue_unitBallCoeff` — Q: [BGR] `bgr-5.1.md:81`
  *"`(Σ a_ν X^ν)~ := Σ ã_ν X^ν ∈ k̃[X]`"* (the image is a polynomial). M: the reduced coefficients have
  finite support. D: the support lies in `{t | 1 ≤ ‖a_t‖}` (`IsLocalRing.residue_eq_zero_iff`, [PFA]
  `maximalIdeal_unitClosedBall`, `mem_openUnitBallIdeal`), finite by L1.14. A: [2] `f = 0`: empty
  support ✓; `σ` infinite ✓ (L1.14 does not need finiteness). [3] no completeness. [5] the three [PFA]
  names verified in `names_chain.lean`. SURVIVED.
- **L2.2** `reductionFun_one`, **L2.4** `reductionFun_zero`, **L2.5** `reductionFun_add` — Q: [Bo]
  `bosch-lectures.txt:384–385` *"the epimorphism `R → k` extends to an epimorphism `π`"*. M: three of
  the four ring-homomorphism laws of `π`. D: `MvPolynomial.ext`, `coeff_reductionFun` (`rfl` in the
  skeleton), `MvPowerSeries.coeff_one`, `MvPolynomial.coeff_one`, `map_add`, `map_zero`, `map_one` of
  `residue`; the subtype equalities by `Subtype.ext`. A: [2] `σ` empty ✓. [3] none. [5] each is a
  coefficientwise identity of at most three rewrites. SURVIVED.
- **L2.3** `reductionFun_mul` — Q: as L2.2 (`π` is a ring homomorphism). M: multiplicativity. D:
  `MvPowerSeries.coeff_mul` and `MvPolynomial.coeff_mul` are both sums over
  `Finset.antidiagonal t`; `map_sum`, `map_mul` of `residue`; the coefficient of the product in the
  subring is the sum of products of `unitBallCoeff`s (`Subtype.ext`, `AddSubmonoidClass.coe_finsetSum`).
  A: [1] is the reduction multiplicative when the product has norm `< 1` but the factors have norm
  one? It cannot happen (the norm is multiplicative), and the identity does not depend on it ✓. [2]
  `f = 0` ✓. [4] BGR calls `~` "a map" and derives multiplicativity of the norm *from* `Tₙ~ = k̃[X]`
  being a domain; the Lean order is the reverse (the floor has `NormMulClass` already), which is
  harmless: the ring-homomorphism property is used by BGR in the same proof (`bgr-5.1.md:83–84`).
  [5] verified names. SURVIVED.
- **L2.6** `reduction_eq_zero_iff` — Q: [Bo] `bosch-lectures.txt:390–391` *"Note that `f̃ = 0` if and
  only if `|f| < 1`."* M: literal. D: `MvPolynomial.ext_iff`, `coeff_reduction`,
  `residue_eq_zero_iff`, [PFA] `maximalIdeal_unitClosedBall`, L1.12 with `ε = 1`. A: [2] `f = 0` ✓.
  [3] none. SURVIVED.
- **L2.7** `norm_eq_one_of_reduction_ne_zero` — Q: [RM] §0.1.2 *"an element of `T̊ₙ` whose reduction is
  nonzero has Gauss norm one"*. M: literal. D: L2.6 and [PFA] `Subring.norm_le_one`. SURVIVED ([2]
  none to instantiate; [3] the hypothesis is used; [5] two lemmas).
- **L2.8** `ker_reduction` — Q: [BGR] `bgr-5.1.md:83` *"Obviously the kernel of this map is `Tₙˇ`"*.
  M: literal, as an equality of ideals of `T⁰`. D: `Ideal.ext`, `RingHom.mem_ker`, L2.6,
  `mem_openUnitBallIdeal`. SURVIVED ([2] zero ideal direction ✓; [4] exact; [5] three lemmas).
- **L2.9** `norm_toRestricted_map_subtype_le_one` — Q: [Bo] `bosch-lectures.txt:382–384` *"the
  `R`-algebra of all restricted power series `f ∈ Tₙ` having coefficients in `R` or, equivalently,
  with `|f| ≤ 1`"*. M: a polynomial over `K⁰` lies in `T⁰` (needed to *define*
  `ofUnitBallPolynomial`, which is complete in the skeleton). D: L1.11, `val_toRestricted`,
  `MvPolynomial.coeff_coe`, `MvPolynomial.coeff_map`, `Subring.norm_le_one`. SURVIVED ([2] `p = 0` ✓;
  [3] none; [5] verified names).
- **L2.10** `reduction_ofUnitBallPolynomial` — Q: [BGR] `bgr-5.1.md:81`. M: on polynomials the
  reduction is `MvPolynomial.map residue`. D: `MvPolynomial.ext`, `coeff_reduction`,
  `MvPolynomial.coeff_map`, and the coefficient computation of L2.9. SURVIVED ([2] constants ✓; [4]
  this is the definition in the source; [5] same names).
- **L2.11** `exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal` — Q: [BGR] `bgr-5.1.md:83` *"and
  the map is surjective"* in the form the source uses it later (`bgr-5.2.md:78–82`: *"there is a
  natural ring epimorphism `τ_ε : T̊ₙ → k̃_ε[X₁, …, Xₙ]` with `ker τ_ε = {f ∈ Tₙ ; |f| ≤ ε}`"*, i.e.
  every series is a polynomial up to a small series). M: `T⁰ = K⁰[X] + T⁰⁰`. D: `p` := the sum of the
  monomials `a_t X^t` over the finite set of L1.14 (`ε = 1`); the difference has all coefficients of
  norm `< 1` (L1.12). A: [2] `f ∈ T⁰⁰`: `p = 0` ✓. [3] none. [5] four lemmas, so this is its own leaf
  and not folded into L2.12. SURVIVED.
- **L2.12** `reduction_surjective` — Q: [BGR] `bgr-5.1.md:83`. M: literal. D:
  `MvPolynomial.map_surjective`, `IsLocalRing.residue_surjective`, L2.10. SURVIVED ([2] `q = 0` ✓;
  [5] verified).
- **L2.13** `reductionEquiv_mk` — Q: [BGR] 5.1.2/2 `bgr-5.1.md:69` *"`T̃ₙ = k̃[X]`"*. M: the
  isomorphism `reductionEquiv` (complete in the skeleton from L2.8 and L2.12) sends a class to the
  reduction. D: `RingEquiv.trans_apply`, `Ideal.quotEquivOfEq_mk`,
  `RingHom.quotientKerEquivOfSurjective_apply_mk` (or `rfl`). SURVIVED ([5]
  `Ideal.quotEquivOfEq_mk` verified; the internal node `reductionEquiv` is N2 below).
- **L2.14** `isPowerBounded_iff_forall_norm_coeff_le_one` — Q: [BGR] `bgr-5.1.md:86` *"`T̊ₙ = Tₙ°`"*;
  [RM] §0.1.2 *"prove that they are the power-bounded and the topologically nilpotent elements of
  `Tₙ` in the sense of mathlib4#40013 (coefficientwise criteria)"*. M: literal, for a nontrivially
  normed field. D: [PFA] `PowerBounded.isPowerBounded_iff_norm_le_one` (needs `NormMulClass` and
  `(𝓝[≠] 0).NeBot` on the Tate algebra: both floor instances, the second from
  `NormedField.nhdsNE_neBot`) and L1.11. A: [1] over a trivially normed field the topology is discrete, every
  element is power-bounded and every coefficient has norm `≤ 1`, so the statement stays true there;
  the hypothesis is kept because the [PFA] lemma is stated with the punctured-neighbourhood instance.
  [3] `NontriviallyNormedField` is what [RM] convention 1 assumes; completeness is not needed. [5]
  verified. SURVIVED.
- **L2.15** `isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one` — Q: [BGR] `bgr-5.1.md:86`
  *"`Ťₙ = Tₙˇ`"*. M: literal, over any normed field. D: [PFA]
  `isTopologicallyNilpotent_iff_norm_lt_one` (`NormMulClass` only) and L1.12. SURVIVED ([2] trivially
  normed `K`: `‖f‖ < 1` iff `f = 0` iff nilpotent ✓; [5] verified).
- **L2.16** `isUnit_iff_norm_coeff_lt` — Q: [Bo] 1.2/4 `bosch-lectures.txt:432–435` *"an arbitrary
  series `f ∈ Tₙ` is a unit if and only if `|f − f(0)| < |f(0)|`, i.e., if and only if the absolute
  value of the constant coefficient of `f` is strictly bigger than the one of all other coefficients
  of `f`."* M: literal (`coeff 0 f ≠ 0` is automatic from the strict inequality when `σ` is nonempty
  and is what makes the statement right for `σ` empty). D: [SEAM] `Restricted.isUnit_iff` at `c = 1`,
  `constantCoeff_eq_coeff_zero`, `isUnit_iff_ne_zero`, the product identity. A: [2] `σ` empty: `f` is
  a constant, unit iff nonzero ✓ — this is why `coeff 0 f.1 ≠ 0` is a separate conjunct; `f = 0` ✓.
  [3] completeness is needed for `←` (Neumann series). [5] `Restricted.isUnit_iff` requires
  `NormMulClass`, `NormOneClass`, `CompleteSpace` on `K`: all present. SURVIVED.
- **L2.17** `isUnit_iff_isUnit_reduction` — Q: [RM] §0.1.2 *"a unit of `T̊ₙ` reduces to a unit, an
  element of `T̊ₙ` whose reduction is a unit is a unit"*. M: literal, as an iff for units *of `T⁰`*.
  D: [PFA] `NormedRing.isUnit_iff_isUnit_mk`, L2.13, `isUnit_map_iff` for the ring isomorphism
  (instance `isLocalHom_equiv`). A: [1] `f = p` over `ℚ_p`: not a unit of `T⁰`, reduction `0` ✓. [3]
  completeness needed. [5] `isUnit_map_iff` carries `[IsLocalHom f]`; the instance for an equivalence
  exists (`isLocalHom_equiv`, verified). SURVIVED.
- **L2.18** `isUnit_coe_iff_isUnit_reduction` — Q: [BGR] 5.1.3/1 `bgr-5.1.md:97` *"Thus `f` is a
  unit if and only if `f̃` is a unit (i.e., a constant) in `T̃ₙ`"*, for `|f| = 1`. M: literal. D:
  L2.17; for `→`, the inverse `g` of `f` in `T` has `‖g‖ = 1` by `norm_mul` and `norm_one`, hence lies
  in `T⁰` (BGR `bgr-5.1.md:101–102` *"is a unit in `Tₙ` if and only if it is a unit in `T̊ₙ`"*). A:
  [1] without `‖f‖ = 1` the statement is false: `f = p` is a unit of `T` with reduction `0` ✓ the
  hypothesis is necessary. [2] `σ` empty ✓. [5] two lemmas and one norm computation. SURVIVED.
- **L2.19** `exists_norm_eq_one_not_isUnit_C_add` — Q: [BGR] 5.1.3/2 `bgr-5.1.md:108–114` *"For each
  `f ∈ Tₙ` with `|f| = 1`, there is an element `c ∈ k` with `|c| = 1` such that `c + f` is not a unit
  in `Tₙ`. Proof. We shall treat the two cases `|f(0)| < 1` and `|f(0)| = 1` separately. If
  `|f(0)| < 1`, then `|f| = 1` implies `|f − f(0)| = 1`. For `g := 1 + f ∈ Tₙ`, we have `|g| = 1` and
  `|g − g(0)| = |f − f(0)| = 1`. … If `|f(0)| = 1`, define `g := f − f(0)`. Then `g(0) = 0`, and hence
  `g` cannot be a unit in `Tₙ`."* M: literal. D: L2.16 in both cases; L1.10 to find a nonconstant
  coefficient of norm one in the first case; `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` for
  `‖1 + f(0)‖ = 1`. A: [2] `σ` empty: `f` constant of norm one, second case, `c + f = 0` ✓. [3] only
  the forward direction of L2.16 is used, which needs no completeness; the section carries it anyway.
  [4] exact. SURVIVED.
- **L2.20** `jacobson_bot` — Q: [BGR] 5.1.3/3 `bgr-5.1.md:118–124` *"`⋂_{𝔪 ∈ Max Tₙ} 𝔪 = (0)` …
  Assume that there is a non-zero series `f` contained in all maximal ideals of `Tₙ`. We may assume
  that `|f| = 1`. Choose `c ∈ k` with `|c| = 1` such that `c + f` is a non-unit. Then we can find a
  maximal ideal `𝔪` such that `c + f ∈ 𝔪`. By assumption, `f` also is an element of `𝔪`. This
  implies `c ∈ 𝔪`, which is impossible since `c ∈ k*`."* M: `Ideal.jacobson ⊥ = ⊥`. D:
  `Ideal.mem_jacobson_bot` (`x ∈ jacobson ⊥ ↔ ∀ y, IsUnit (x * y + 1)`) with `y = C c⁻¹`; L1.16 to
  normalise; L2.19. A: [2] `σ` empty: a field, `jacobson ⊥ = ⊥` ✓. [3] `σ` need not be finite. [4]
  the Lean proof replaces "find a maximal ideal" by the unit characterisation — same content. [5]
  `Ideal.mem_jacobson_bot` verified. SURVIVED.

### Internal nodes

- **N2** `reduction` (the ring homomorphism, complete in the skeleton from L2.2–L2.5) and
  `reductionEquiv` (complete from L2.8, L2.12) — source [BGR] 5.1.2/2. [6] could the four laws hold
  and `reduction` fail to be the source's map? Its coefficient formula `coeff_reduction` is `rfl`, so
  it is the source's map by definition ✓. [2] `K` trivially normed: `K⁰ = K`, `K⁰⁰ = 0`, the
  reduction is the identity on polynomials and `T = K[X]` ✓. [4] BGR's `T̃ₙ` is defined with
  power-bounded and topologically nilpotent elements; L2.14–L2.15 identify them with `T⁰`, `T⁰⁰`, as
  BGR does at `bgr-5.1.md:86`. SURVIVED.

---

## G3 — Evaluation of restricted power series (`TateAlgebra/Eval.lean`), [RM] Layer 0 preamble

### Source and prose proof

[BGR] 5.1.4 (`bgr-5.1.md:219–223`, `:250–255`): *"Since `a_ν x^ν` is a zero-sequence in `L`, the
series `Σ a_ν x^ν` must converge to some element in `L`. Thus we see that, for all `x ∈ Bⁿ(k_a)`, the
element `f(x)` is well-defined … **Proposition 2.** Let `f` be a series in `Tₙ`. Then
`sup_{x ∈ Bⁿ(k_a)} |f(x)| ≤ |f|` … Proof. For all `x ∈ Bⁿ(k_a)` and all `ν`, we have
`|a_ν x^ν| ≤ |a_ν| ≤ |f|` if `f = Σ a_ν X^ν`. Therefore, `|f(x)| ≤ max |a_ν x^ν| ≤ |f|` …
Furthermore, `f` is a uniform limit of polynomials and hence continuous."* [BGR] 5.1.3/5
(`bgr-5.1.md:149–156`): *"For `Σ a_ν X^ν ∈ k[X]`, one clearly has
`φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}`. Due to the theorem, `φ` is continuous, and therefore
`φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}` for all `Σ a_ν X^ν ∈ Tₙ`. Thus `φ` is uniquely determined by
the tuple `(φ(X₁), …, φ(Xₙ))`. Now let `f₁, …, fₙ ∈ T̊ₘ` be given. Then it is easy to verify that
`φ : Tₙ → Tₘ` defined by `φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}` is a `k`-algebra homomorphism with
`φ(Xᵢ) = fᵢ`."*

Both constructions of the source — evaluation at a point of a complete extension field and
substitution of power-bounded series — are one statement: for a complete nonarchimedean normed
commutative ring `B`, a contractive ring homomorphism `φ : R → B` and a tuple `x` with `‖x i‖ ≤ c i`,
the terms `φ(a_ν) x^ν` are bounded by the Gauss terms `‖a_ν‖ c^ν`, hence tend to zero, hence are
summable; the sum is additive, sends `1` to `1`, and is multiplicative by the Cauchy product (a
product of two null families is null on the product index set, [PFA] `summable_prod_map₂`); it is
bounded by the Gauss norm termwise, hence continuous; and a continuous ring homomorphism is
determined on the dense subring of polynomials (L1.7), i.e. by the constants and the variables.
⚠ [RM] says this is supplied by the adic-spaces roadmap; it is not in this chain, so the board
supplies it (erratum E10).

### Leaves

- **L3.1** `norm_map_mul_prod_pow_le` — Q: [BGR] `bgr-5.1.md:253` *"we have `|a_ν x^ν| ≤ |a_ν| ≤ |f|`"*.
  M: the first inequality, at a general polyradius: `‖φ(a) x^t‖ ≤ ‖a‖ c^t`. D: `norm_mul_le`, `hφ`,
  and for `t ≠ 0` `Finset.norm_prod_le'` (nonempty support), `norm_pow_le'` (positive exponents on
  the support), `pow_le_pow_left₀`, `Finset.prod_le_prod`. A: [2] `t = 0`: the product is `1` and
  `‖1‖` need not be `≤ 1` in `B` — so the case `t = 0` is done by `mul_one` *before* taking norms;
  the statement is still true ✓ (this is why `B` needs no `NormOneClass`). [3] no ultrametric
  hypothesis is used (the skeleton `omit`s both). [5] five lemmas with a case split — at the limit
  for a leaf; kept as one statement because the split is on `t` only. SURVIVED.
- **L3.2** `tendsto_map_coeff_mul_prod_pow` — Q: [BGR] `bgr-5.1.md:221` *"`a_ν x^ν` is a zero-sequence
  in `L`"*. M: literal, along the cofinite filter. D: `squeeze_zero_norm'` with L3.1 and `f.2`.
  SURVIVED ([2] `f = 0` ✓; [3] `B` need not be complete or ultrametric; [5] two lemmas).
- **L3.3** `summable_map_coeff_mul_prod_pow` — Q: [BGR] `bgr-5.1.md:221–222` *"the series
  `Σ a_ν x^ν` must converge to some element in `L`"*. M: literal. D:
  `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` and L3.2. SURVIVED ([3] completeness of
  `B` necessary; [5] verified).
- **L3.4** `eval₂Fun_zero`, **L3.5** `eval₂Fun_one`, **L3.6** `eval₂Fun_add` — Q: [BGR]
  `bgr-5.1.md:153–155` *"it is easy to verify that `φ` … is a `k`-algebra homomorphism"*. M: three of
  the four laws. D: `tsum_zero`; `tsum_eq_single 0` with `MvPowerSeries.coeff_one`;
  `Summable.tsum_add` with L3.3. A: [2] `eval₂Fun_one` and `_zero` hold with no hypothesis on `c`,
  `φ`, `x` (a `tsum` with one nonzero term needs no summability) — the skeleton `omit`s them ✓. [3]
  `_add` needs summability, hence `hφ`, `hx`, completeness. [5] verified. SURVIVED.
- **L3.7** `eval₂Fun_mul` — Q: as L3.4 (*"`k`-algebra homomorphism"*), and [BGR] `bgr-2.md:56–59`
  for the product being the Cauchy product (*"we define their 'Cauchy product' `f·x` by
  `f·x := Σ_λ (Σ_{μ+ν=λ} a_μ x_ν) X^λ`"*). M: multiplicativity. D:
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` with the product-summability hypothesis from
  [PFA] `IsUltrametricDist.summable_prod_map₂` (`b := (· * ·)`, `norm_mul_le`);
  `MvPowerSeries.coeff_mul`, `map_sum`, `map_mul`, `Finsupp.prod_add_index'`, `Finset.sum_mul`. A: [1]
  ⚠ Mathlib's `Summable.mul_of_nonarchimedean` needs `NonarchimedeanRing B`, and an ultrametric
  normed ring has **no** such instance at the pin (`inferInstance` fails, `names_mathlib4.lean`), so
  the discharge goes through the chain's lemma; `Eval.lean` gains
  `import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums`. [2] `f = 0` ✓. [3] commutativity of `B` is
  used to reorder `x^{t₁} φ(b)`. [5] six lemmas: this leaf is the one substantial computation of the
  file and is a ticket of its own. SURVIVED.
- **L3.8** `eval₂_monomial`, **L3.9** `eval₂_C`, **L3.10** `eval₂_X` — Q: [BGR] `bgr-5.1.md:155`
  *"with `φ(Xᵢ) = fᵢ`"*. M: the values on monomials, constants and variables. D: `tsum_eq_single`,
  `MvPowerSeries.coeff_monomial`, `coeff_C`, `coeff_X`, `Finsupp.prod_single_index`,
  `Finsupp.prod_zero_index`. SURVIVED ([2] `a = 0` ✓; [5] verified).
- **L3.11** `eval₂_toRestricted` — Q: [BGR] `bgr-5.1.md:150–151` *"For `Σ a_ν X^ν ∈ k[X]`, one clearly
  has `φ(Σ a_ν X^ν) = Σ a_ν f₁^{ν₁} … fₙ^{νₙ}`"*. M: on polynomials evaluation is
  `MvPolynomial.eval₂`. D: `MvPolynomial.ringHom_ext` on the two ring homomorphisms, L3.9, L3.10,
  `toRestricted_C`, `toRestricted_X`, `MvPolynomial.eval₂_C`, `eval₂_X`. SURVIVED ([5] verified).
- **L3.12** `norm_eval₂_le` — Q: [BGR] 5.1.4/2 `bgr-5.1.md:254` *"Therefore,
  `|f(x)| ≤ max |a_ν x^ν| ≤ |f|`"*. M: literal. D:
  `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, L3.1, L1.1. SURVIVED ([2] `f = 0` ✓; [3]
  ultrametricity of `B` necessary — over `ℝ` the sum of the terms can exceed the maximum; [5]
  verified).
- **L3.13** `continuous_eval₂` — Q: [BGR] `bgr-5.1.md:255` *"`f` is a uniform limit of polynomials and
  hence continuous"*; `:151` *"`φ` is continuous"*. M: continuity of the homomorphism `f ↦ f(x)`. D:
  `AddMonoidHomClass.continuous_of_bound` with bound `1` and L3.12. A: [4] the quoted sentence is
  about continuity in `x`; the leaf is continuity in `f`, which is what 5.1.3/5 uses ("Due to the
  theorem, `φ` is continuous"). Continuity in `x` is not claimed by the board. SURVIVED.
- **L3.14** `ringHom_ext_of_continuous`, **L3.19** `algHom_ext_of_continuous` — Q: [BGR]
  `bgr-5.1.md:152–153` *"Thus `φ` is uniquely determined by the tuple `(φ(X₁), …, φ(Xₙ))`"*. M:
  literal: two continuous homomorphisms into a Hausdorff ring that agree on constants and variables
  are equal. D: `DenseRange.equalizer` with L1.7 and `MvPolynomial.ringHom_ext`; the algebra form by
  `AlgHom.commutes` and [SEAM] `algebraMap_apply`. A: [1] can continuity be dropped? Not for an arbitrary
  target: BGR obtains it from 5.1.3/4, which is specific to homomorphisms between Tate algebras
  (`bgr-5.1.md:126–127`), so for a general Hausdorff target it is a hypothesis ✓. [3] `T2Space B` is
  necessary for the equalizer to be closed. [5] verified. SURVIVED.
- **L3.15** `aeval_X`, **L3.16** `aeval_toRestricted`, **L3.17** `norm_aeval_le`, **L3.18**
  `continuous_aeval` — the `K`-algebra forms of L3.10–L3.13; Q as there. D: `aeval` unfolds to
  `eval₂` along `algebraMap K B`, contractive by `norm_algebraMap'` (this needs `NormOneClass B`,
  present); `MvPolynomial.aeval_def`. A: [2] `B = K` ✓; `B` a Tate algebra ✓ (instances from G1).
  [3] `NormOneClass B` cannot be dropped: `‖algebraMap a‖ = ‖a‖ ‖1‖`. [5] verified. SURVIVED.

### Internal node

- **N3** `eval₂` and `aeval` (complete in the skeleton from L3.4–L3.7 and L3.9) — source [BGR]
  5.1.3/5, 5.1.4. [6] children true and parent false: the ring-homomorphism fields are exactly
  L3.4–L3.7; `commutes'` of `aeval` is L3.9 with [SEAM] `algebraMap_apply` ✓. [2] `σ` empty: `eval₂`
  is `φ` on constants ✓. [4] the source evaluates at points of the unit ball and substitutes
  power-bounded series; both are instances (`B = L`, `B = Tₘ`), compiled in `spot3.lean`. SURVIVED.

---

## G4 — Reduction commutes with evaluation (`TateAlgebra/EvalReduction.lean`), [RM] §0.1.3

### Source and prose proof

[BGR] 5.1.4 (`bgr-5.1.md:257–266`): *"Let `~ : Bⁿ(k_a) = k̊_aⁿ → k̃_aⁿ` denote the obvious extension
of the residue map `~ : k̊ → k̃`. It is easy to see that the following diagram … is commutative for
all `f ∈ T̊ₙ`. (In the diagram, `f̃` stands for the map induced by the polynomial
`f̃ ∈ k̃_a[X₁, …, Xₙ]`.)"* [Bo] 1.2/5 (`bosch-lectures.txt:449–456`): *"Choosing a lifting
`x ∈ Bⁿ(K̄)` of `x̃`, we can consider the commutative diagram … where the first vertical map is
evaluation at `x` and the second one evaluation at `x̃`. As `f(x) ∈ R̄` is mapped onto
`f̃(x̃) ∈ k̄`, which is non-zero, we obtain `|f(x)| = 1 = |f|`"*. For substitutions, [BGR]
`bgr-5.2.md:244`: *"`(σ(f))~ = σ̃(f̃)`"*.

Both sides of each square are ring homomorphisms out of `T⁰` that vanish on `T⁰⁰` (the left one
because evaluation is contractive, L3.17; the right one by L2.6). Every element of `T⁰` is a
polynomial over `K⁰` modulo `T⁰⁰` (L2.11), so it suffices to compare the two sides on polynomials
over `K⁰`, where both are ring homomorphisms out of a polynomial ring and agree on constants and
variables (L3.16, L2.10).

### Leaves

- **L4.1** `instance : IsLocalHom (NormedField.unitClosedBallMap K L)` — Q: [BGR] `bgr-5.1.md:257`
  *"the residue map `~ : k̊ → k̃`"* extended to an extension field (the diagram needs
  `k̃ → k̃_a`). M: glue: the map `K⁰ → L⁰` is local, so `ResidueField.map` applies. D: [PFA]
  `isUnit_iff_norm_eq_one` in `K` and in `L`, `norm_algebraMap'`. SURVIVED ([2] `L = K` ✓; [3] `L`
  must be a normed field so that `‖algebraMap a‖ = ‖a‖`; [5] verified).
- **L4.2** `norm_aeval_le_one` — Q: [BGR] `bgr-5.1.md:265` *"for all `f ∈ T̊ₙ`"* (the top arrow of the
  diagram lands in `k̊_a`). M: evaluation maps `T⁰` to `B⁰`. D: L3.17, `Subring.norm_le_one`.
  SURVIVED ([5] two lemmas).
- **L4.3** `residue_aeval` — Q: [BGR] `bgr-5.1.md:257–266` (the commutative diagram); [Bo]
  `bosch-lectures.txt:455` *"`f(x) ∈ R̄` is mapped onto `f̃(x̃) ∈ k̄`"*. M: the residue class of `f(x)`
  is `f̃(x̃)`, with `f̃` transported along `K̃ → L̃` (`MvPolynomial.eval₂ (residueFieldMap K L)`). D:
  the argument above: L2.11, L3.17 and L2.6 for the vanishing on `T⁰⁰`, then
  `MvPolynomial.ringHom_ext`, L3.16, L2.10, `IsLocalRing.ResidueField.map_residue`,
  `MvPolynomial.eval₂_map`. A: [1] for `L` not complete `aeval` is undefined — `L` is complete in the
  statement ✓. [2] `σ` empty ✓ (constants); `x = 0` ✓. [4] the source states it for `k_a`; the leaf
  for any complete normed extension field, which is what the source's remark at `bgr-5.1.md:272–273`
  needs. [5] six lemmas in two stages; the first stage is a private lemma "two ring homomorphisms out
  of `T⁰` that vanish on `T⁰⁰` and agree on `K⁰[X]` are equal", shared with L4.4. SURVIVED.
- **L4.4** `reduction_aeval` — Q: [BGR] `bgr-5.2.md:244` *"`(σ(f))~ = σ̃(f̃)`"*; `bgr-5.1.md:165–166`
  *"The `k`-algebra homomorphisms `φ` and `φ⁻¹` induce `k̃`-algebra homomorphisms
  `φ̃ : k̃[X₁, …, Xₙ] → k̃[X₁, …, Xₘ]`"*. M: for a substitution `X i ↦ x i` with `x i ∈ Tₘ⁰`, the
  reduction of `f(x)` is `f̃` evaluated at the reductions of the `x i`. D: the private lemma of L4.3,
  then `MvPolynomial.ringHom_ext`, L3.16, L2.10, and the reduction of a constant (`coeff_reduction`,
  `val_C`, `MvPowerSeries.coeff_C`, `MvPolynomial.coeff_C`). A: [2] `τ` empty: the target is `K`,
  and the statement is L4.3 for `L = K` ✓. [3] completeness of `K` is needed for the target Tate
  algebra to be complete. [5] same shape as L4.3. SURVIVED.

---

## G5 — The supremum seminorm (`SupSeminorm.lean`), [RM] conventions 4–5, §0.1.3–§0.1.4

### Source and prose proof

[BGR] 3.8.1/1–2 (`bgr-3.8.md:25–35`): *"For `x ∈ Max_k A` and `f ∈ A`, denote by `f(x)` the image of
`f` under the canonical residue epimorphism `π_x: A → A/x`. Since `A/x` is an algebraic extension of
`k`, it can be provided with the spectral norm derived from the given valuation on `k` … Writing
`|f(x)|` for the spectral norm of the element `f(x) ∈ A/x` … `|f|_sup := 0` if `Max_k A = ∅`,
`sup {|f(x)|; x ∈ Max_k A}` if `Max_k A ≠ ∅` and `f(Max_k A)` bounded"*. [BGR] 3.8.2/1–2
(`bgr-3.8.md:122–126`, `:147–149`): *"`|f(x)| = inf_{i∈ℕ} |f(x)^i|_res^{1/i} ≤ |f(x)|_res ≤ |f|` …
**Corollary 2.** If `A` is a `k`-Banach algebra with norm `| |`, then for all `f ∈ A` one has
`|f|_sup ≤ |f|`."* [Bo] 1.2/12 (`bosch-lectures.txt:655–671`): *"we assume there is an element
`a ∈ Tₙ` with `|φ(a)| > |a|`. … Write `α = φ(a)`, and let `f(η) = η^r + c₁η^{r−1} + … + c_r ∈ K[η]`
be the minimal polynomial of `α` over `K`. … As `K` is complete and the absolute value of `K` extends
uniquely to `K(α)`, we get `|α_j| = |α|` for all `j`. In particular, we have `|c_r| = |α|^r` and
`|c_j| ≤ |α|^j < |α|^r = |c_r|` for `j < r` … the expression `f(a) = a^r + c₁a^{r−1} + … + c_r` is a
unit in `Tₙ` and, consequently, it must be mapped under `φ` to a unit … On the other hand, the image
`φ(f(a))` is trivial, as it equals `φ(f(a)) = f(α) = 0`. Thus, we obtain a contradiction"*. [BGR]
5.1.4/6 (`bgr-5.1.md:319–322`): *"Thus `𝔪_x := ker h_x` is a `k`-algebraic maximal ideal in `Tₙ`, and
`Tₙ/𝔪_x` is isomorphic to `L` over `k`. Corresponding elements in `Tₙ/𝔪_x` and `L` must have the same
spectral norm over `k` so that `|g(𝔪_x)| = |g(x)|` for all `g ∈ Tₙ`."*

`|f(x)|` is written `spectralValue (minpoly K (mk f))`, which is `spectralNorm K (A ⧸ x) (mk f)` by
definition and needs no `Field` instance on the quotient ([RM] convention 4; clarification E11). At a
maximal ideal whose residue class of `f` is not algebraic the minimal polynomial is `0` and the value
is `0`, so the supremum over *all* maximal ideals is BGR's supremum over `Max_k A`, with BGR's value
`0` when that set is empty. The inequality `|f(x)| ≤ ‖f‖` is proved by Bosch's unit argument rather
than through the residue norm of BGR 3.8.2/1 (which would need closed maximal ideals, residue norms
and the uniqueness of power-multiplicative norms): if `σ := |f(x)| > ‖f‖`, the minimal polynomial `q`
of the residue class is irreducible over the complete field `K`, so `σ = |q(0)|^{1/r}` and
`|q_n| ≤ σ^{r−n}`; then `q(f) = q(0) + (terms of norm < σ^r = |q(0)|)` is a unit of the Banach algebra
`A` (Neumann series), and it lies in the proper ideal `x`. The normalisation `|a| = 1` of Bosch's
proof is not needed and is not available in a general Banach algebra.

### Leaves

- **L5.1** `evalNorm_nonneg` — Q: [BGR] `bgr-3.8.md:27–28` *"Writing `|f(x)|` for the spectral norm"*.
  M: nonnegativity of the value. D: `spectralValue_nonneg`. SURVIVED ([2] non-algebraic class: the
  value is `spectralValue 0 = 0` ✓; [3] no hypothesis on `K` beyond a norm; [5] verified).
- **L5.2** `evalNorm_eq_zero_of_mem` — Q: [BGR] `bgr-7.1.1.md:11–12` *"we have `|f(𝔪)| = 0`, if and
  only if `f(𝔪) = 0`, i.e., `f ∈ 𝔪`"*. M: the direction `f ∈ x → |f(x)| = 0`. D:
  `Ideal.Quotient.eq_zero_iff_mem`, `minpoly.zero`, `spectralValue_X_pow` at exponent `1`. A: [2]
  `f = 0` ✓. [3] the converse needs the spectral norm to be a norm on the residue field (complete
  `K`, algebraic class); it is not claimed here and is Layer 3 ([RM] §3.1). [5] `minpoly.zero` needs
  `Nontrivial (A ⧸ x)`, true for a maximal ideal. SURVIVED.
- **L5.3** `isMaximal_ker_of_isAlgebraic` — Q: [BGR] `bgr-5.1.md:319–320` *"Thus `𝔪_x := ker h_x` is
  a `k`-algebraic maximal ideal in `Tₙ`"*. M: for any `K`-algebra homomorphism into an algebraic
  extension field, not necessarily surjective. D: the range is a subalgebra of an algebraic field
  extension, hence a field (`Subalgebra.isField_of_algebraic`);
  `Ideal.quotientKerAlgEquivOfSurjective` onto the range; `Ideal.Quotient.maximal_of_isField`. A: [1]
  BGR uses surjectivity of `h_x`; without it the range is still a field because `L` is algebraic ✓.
  [2] `A = K` ✓. [3] algebraicity is necessary: `K[X] → K(X)` has kernel `0`, not maximal. [5]
  verified. SURVIVED.
- **L5.4** `finite_quotient_ker` — Q: [BGR] `bgr-5.1.md:314` *"Then `L` is finite over `k`"* and
  `:320–321` *"`Tₙ/𝔪_x` is isomorphic to `L` over `k`"*. M: the residue field at the kernel is finite
  over `K`. D: `Ideal.kerLiftAlg_injective`, `FiniteDimensional.of_injective`. SURVIVED ([3]
  finite-dimensionality of `L` is used; [5] verified).
- **L5.5** `evalNorm_eq_norm_algHom` — Q: [BGR] `bgr-5.1.md:321–322` *"Corresponding elements in
  `Tₙ/𝔪_x` and `L` must have the same spectral norm over `k` so that `|g(𝔪_x)| = |g(x)|` for all
  `g ∈ Tₙ`."* M: literal, with the norm of `L` in place of the spectral norm (they agree over a
  complete field). D: `Ideal.Quotient.liftₐ` is injective because its kernel is `x`;
  `minpoly.algHom_eq`; `NormedAlgebra.norm_eq_spectralNorm`. A: [1] is `‖·‖` on `L` forced to be the
  spectral norm? Only over a complete `K` — the statement assumes `[CompleteSpace K]` and
  `NontriviallyNormedField K`, exactly the hypotheses of the Mathlib lemma ✓. [2] `φ f = 0`: both
  sides `0` ✓. [3] `hx` lets the consumer choose the maximal ideal; no surjectivity of `φ` needed.
  [5] the Mathlib statement is `‖x‖ = spectralNorm K L x` with `[NontriviallyNormedField K]
  [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
  [CompleteSpace K]` (printed in `names_mathlib4.out`). SURVIVED.
- **L5.6** `evalNorm_le_norm` — Q: [BGR] 3.8.2/1 `bgr-3.8.md:126` *"`… ≤ |f(x)|_res ≤ |f|`"* (the
  statement); [Bo] `bosch-lectures.txt:655–671` (the proof, quoted above). M: `|f(x)| ≤ ‖f‖` for
  every maximal ideal of a Banach `K`-algebra. D: by contradiction with `σ := evalNorm K x f > ‖f‖`;
  `minpoly.eq_zero` disposes of the non-integral case; `minpoly.irreducible`, `minpoly.monic`;
  `AdjoinRoot.minpoly_root` and `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` give
  `σ = ‖q.coeff 0‖ ^ (1 / r)`; `spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_bddAbove`,
  `le_ciSup` give `‖q.coeff n‖ ≤ σ ^ (r − n)`; `Polynomial.aeval_eq_sum_range`,
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_pow_le'`, `pow_lt_pow_left₀`,
  `isUnit_one_sub_of_norm_lt_one`; `Polynomial.aeval_algHom_apply`, `minpoly.aeval`,
  `Ideal.eq_top_of_isUnit_mem`. A: [1] is it true for a Banach algebra whose norm is not
  power-multiplicative? Yes: the argument only uses `‖fⁿ‖ ≤ ‖f‖ⁿ`. [2] `A = 0`: no maximal ideal,
  vacuous ✓; `f = 0`: `0 ≤ 0` ✓; `f ∈ x`: `0 ≤ ‖f‖` ✓; non-algebraic residue class: value `0` ✓. [3]
  completeness of `A` is necessary (BGR `bgr-3.8.md:151–152`: *"take `A = k[X]` provided with the
  Gauss norm and `f := X`; then `|X| = 1`, whereas `|f|_sup = ∞`"*); completeness of `K` is used for
  `σ = ‖q(0)‖^{1/r}`; `NormOneClass A` is **not** needed. [4] the leaf is BGR's statement and Bosch's
  proof, generalised from `Tₙ` to Banach algebras by replacing "Corollary 4" with the Neumann series.
  [5] the longest discharge on the board — a ticket of its own, with the three displayed
  inequalities as private lemmas. SURVIVED.
- **L5.7** `bddAbove_range_evalNorm` — Q: [BGR] `bgr-3.8.md:34` *"`f(Max_k A)` bounded"*. M: the
  family of values is bounded, by `‖f‖`. D: L5.6. SURVIVED.
- **L5.8** `supSeminorm_le_norm` — Q: [BGR] 3.8.2/2 `bgr-3.8.md:147–149` (quoted above). M: literal.
  D: `ciSup_le` with L5.6 when the maximal spectrum is nonempty, `Real.iSup_of_isEmpty` otherwise. A:
  [2] the zero ring: `0 ≤ 0` ✓ — the real `iSup` over an empty type is `0`, which is BGR's convention.
  [3] as L5.6. SURVIVED.

### Internal nodes

- **N5** the definitions `evalNorm`, `supSeminorm` (complete in the skeleton) — source [BGR]
  3.8.1/1–2. [6] does the junk value agree with the source? At a non-algebraic maximal ideal the
  value is `0`, and BGR excludes such ideals from the supremum; a supremum of nonnegative numbers is
  unchanged by adding zeros, and equals `0` on an empty index set, BGR's first case ✓. BGR's third
  case (`∞` for an unbounded family) becomes the junk value `0` of an unbounded real `iSup`; every
  statement about `supSeminorm` on the board is for a Banach algebra, where L5.7 excludes it ✓. [4]
  [RM] convention 4 says `spectralNorm K (A ⧸ x)`; the code spells it `spectralValue (minpoly …)`,
  the definition of `spectralNorm` (clarification E11). SURVIVED.

---

## G6 — The maximum modulus principle (`TateAlgebra/MaxModulus.lean`), [RM] §0.1.3–§0.1.4

### Source and prose proof

[BGR] 5.1.4/3 (`bgr-5.1.md:270–285`): *"For all `f ∈ Tₙ`, there is an `x ∈ Bⁿ(k_a)` such that
`|f(x)| = |f|`. … These assertions remain valid if `k_a` is replaced by any field extension
`L ⊂ k_a` of `k`, provided `L̃` is infinite. Proof. We may assume `|f| = 1`. Since the residue field
`k̃_a` of `k_a` equals the algebraic closure of `k̃` (see Lemma 3.4.1/4), it has infinitely many
elements. Then there must be a point `x = (x₁, …, xₙ) ∈ Bⁿ(k_a)` such that `f̃(x̃₁, …, x̃ₙ) ≠ 0`,
i.e., `(f(x))~ ≠ 0`, which is equivalent to `|f(x)| = 1`. … The only property of `k_a` (besides being
valued) needed for the proof was the fact that `k̃_a` had to be infinite."* [BGR] 5.1.4/6
(`bgr-5.1.md:310–323`): *"Since `| |_sup ≤ | |` by Corollary 3.8.2/2, we have only to show that, for
each `f ∈ Tₙ`, there exists a `k`-algebraic maximal ideal `𝔪 ⊂ Tₙ` such that `|f(𝔪)| = |f|`. In order
to do this, consider a point `x` … such that `|f(x)| = |f|` (Proposition 3). Denote by
`L := k(x₁, …, xₙ)` the extension of `k` generated by the components of `x`. Then `L` is finite over
`k`, and … there is an evaluation homomorphism `h_x : Tₙ → L`"*.

The proof is BGR's, with one substitution. BGR takes the point in `Bⁿ(k_a)` and needs Lemma 3.4.1/4
(the residue field of `k_a` is the algebraic closure of `k̃`) to find enough residue classes; `k_a`
is not complete, so the evaluation of G3 does not apply to it, and BGR passes to a finite
subextension anyway. The board goes to a finite extension directly: the reduction `f̃` of a series of
norm one is a nonzero polynomial whose degrees in each variable are bounded by some `d`; by the
combinatorial Nullstellensatz it does not vanish on `S̃ⁿ` for any set `S̃` of more than `d` residue
classes; and `m > d` residue classes are supplied by the `m`-th roots of unity in the splitting
field of `X^m − 1`, for `m` of norm one in `K` — they have norm one (a root of a monic polynomial of
Gauss norm one, [BGR] `bgr-3.2.md:76–79`: *"If `f` is monic, we have `σ(f) ≤ |f|` for the spectral
value `σ(f)` of `f`. Hence, in particular, `|α| ≤ |f|` for each root `α ∈ K_a` of `f`"*), and their
pairwise differences have norm one because `∏_{t ≠ s} (s − t) = m s^{m−1}` has norm one and every
factor has norm at most one. This is Lemma 3.4.1/4 for the single polynomial `X^m − 1`, and it is
what the source's remark licenses (*"any field extension … provided `L̃` is infinite"*: the proof uses
only "more residue classes than the degrees of `f̃`"). ⚠ It is the one place where the board proves a
sub-lemma the source cites from elsewhere; see N6.

### Leaves

- **L6.1** `NormedField.exists_lt_natCast_norm_eq_one` — Q: [RM] §0.1.3 *"⚠ The residue field `K̃` may
  be finite, so the point is in general not `K`-rational: the extension is unavoidable"*; the leaf
  supplies the order `m` of the roots of unity. M: in a nonarchimedean field there are natural
  numbers of norm one beyond any bound. D: if `‖(d+1 : K)‖ = 1` take `m = d + 1`; otherwise
  `‖(d+1 : K)‖ < 1` (`IsUltrametricDist.norm_natCast_le_one`) and `m = d + 2` has norm
  `max (‖d+1‖, 1) = 1` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`). A: [1] characteristic
  `p`: `m` is prime to `p` automatically (norm one means nonzero) ✓. [2] `d = 0`: `m ∈ {1, 2}` ✓. [3]
  no completeness, no nontriviality. [5] two lemmas. SURVIVED.
- **L6.2** `exists_finset_splittingField_X_pow_sub_one` — Q: [BGR] `bgr-5.1.md:272–273` *"These
  assertions remain valid if `k_a` is replaced by any field extension `L ⊂ k_a` of `k`, provided `L̃`
  is infinite"* (the licence), and `bgr-3.2.md:76–79` (roots of a monic polynomial of Gauss norm one
  have norm at most one). M: the splitting field of `X^m − 1` contains `m` elements of spectral norm
  one with pairwise differences of spectral norm one. D: `Polynomial.separable_X_pow_sub_C`,
  `Polynomial.SplittingField.splits`, `Polynomial.card_rootSet_eq_natDegree`,
  `Polynomial.natDegree_X_pow_sub_C` for the `m` distinct roots; the normed-field structure
  `spectralNorm.normedField K L` (complete `K`) makes the spectral norm multiplicative, so
  `‖ζ‖^m = ‖ζ^m‖ = 1` gives `‖ζ‖ = 1`; `Polynomial.Splits.eval_root_derivative`,
  `Polynomial.derivative_X_pow`, `spectralNorm_extends`, `isNonarchimedean_spectralNorm` for the
  differences. A: [1] `m` divisible by the residue characteristic would make the roots collapse in
  the residue field (`X^p − 1 ≡ (X − 1)^p`) — excluded by `‖(m : K)‖ = 1` ✓. [2] `m = 1`: `S = {1}`,
  no pairs ✓. [3] `0 < m` needed for `X^m − 1` to have degree `m`; completeness of `K` used for
  multiplicativity of the spectral norm. [4] no source proves this leaf as stated: it is Lemma
  3.4.1/4 specialised to `X^m − 1`, and the proof is the discriminant identity above; recorded as a
  deviation in N6. [5] ⚠ `spectralNorm_pow` does not exist; the power rule is `isPowMul_spectralNorm`
  or the normed-field structure (`names_mathlib4.lean`). SURVIVED.
- **L6.3** `exists_norm_aeval_eq_norm` — Q: [BGR] 5.1.4/3 `bgr-5.1.md:277–280` *"We may assume
  `|f| = 1`. … Then there must be a point `x = (x₁, …, xₙ) ∈ Bⁿ(k_a)` such that
  `f̃(x̃₁, …, x̃ₙ) ≠ 0`, i.e., `(f(x))~ ≠ 0`, which is equivalent to `|f(x)| = 1`."* M: literal, for a
  complete extension field `L` and a finite set `S ⊆ L⁰` with distinct residues and more elements
  than the exponents at the coefficients of maximal norm. D: L1.16 to normalise; L2.7, L2.1 for the
  support of `f̃`; `MvPolynomial.map_injective`, `MvPolynomial.degreeOf_le_iff`,
  `MvPolynomial.degrees_map_le` for the degrees after `K̃ → L̃`; `Finset.card_image_of_injOn` for the
  residues of `S`; `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`; L4.3; L3.17. A: [1] `f = 0`
  with `σ` nonempty: the hypothesis `hf` then forces `S` nonempty (take `t = 0`), any point works ✓;
  with `S = ∅` and `f ≠ 0` the hypothesis fails (`0 < 0`) ✓. [2] `σ` empty: `x` is the empty tuple,
  `f` a constant ✓. [3] `Finite σ` is what the Nullstellensatz lemma needs; `K` need not be complete.
  [4] BGR's "infinitely many elements" is replaced by the exact count the argument uses. [5] the
  Nullstellensatz lemma is `[Finite σ] [IsDomain R] (P) (S : σ → Finset R)
  (∀ i, degreeOf i P < (S i).card) → (∀ x, (∀ i, x i ∈ S i) → eval x P = 0) → P = 0`
  (`names_mathlib4.out`). SURVIVED.
- **L6.4** `exists_evalNorm_eq_norm` — Q: [BGR] 5.1.4/6 `bgr-5.1.md:311–312` *"we have only to show
  that, for each `f ∈ Tₙ`, there exists a `k`-algebraic maximal ideal `𝔪 ⊂ Tₙ` such that
  `|f(𝔪)| = |f|`"*. M: literal, with the finiteness of the residue field recorded. D: L1.14 bounds
  the exponents of the maximal coefficients; L6.1, L6.2; the spectral normed-field structure on the
  splitting field (`spectralNorm.normedField`, `.normedAlgebra`, `.completeSpace`); L6.3; L5.3, L5.4,
  L5.5. A: [2] `f = 0`: L6.3 does not apply (every index is maximal); use the point found for `f = 1`
  and L5.2 ✓. [3] ⚠ [RM] §0.1.3 postpones this item until "the finiteness of the residue fields is
  §1.2.4"; that is unnecessary — the point is constructed with a finite residue field (erratum E4).
  [5] the assembly was compiled against the skeleton (`scratch/spot3.lean`, item 4). SURVIVED.
- **L6.5** `exists_evalNorm_eq_norm_and_notMem` — Q: [RM] §0.1.4 *"the set of `x` with
  `|f(x)| = |f|` is nonempty and Zariski-dense when `f ≠ 0`"*; [BGR] 5.1.4/4 `bgr-5.1.md:292–293`
  *"Use the fact that the Gauss norm is a valuation on `Tₙ` (Proposition 5.1.2/1), and apply
  Proposition 3 to the series `X₁ … Xₙ f`."* M: for `g ≠ 0` some point of maximal modulus for `f`
  lies off the zero set of `g` — the product trick with `g` in place of `X₁ … Xₙ`. D: apply the
  point-level statement inside L6.4 to `f * g`; `norm_mul` on both sides; L3.17 for the two factors;
  L5.5, L5.2. A: [2] `f = 0`: apply L6.4 to `g` alone ✓. [3] `g ≠ 0` necessary. [4] the roadmap's
  "Zariski-dense" is exactly this statement (a closed set `V(g)` with `g ≠ 0` does not contain all
  such points). [5] L6.4's proof must expose the homomorphism `Tₙ → L` (a private lemma), since
  multiplicativity of `evalNorm` at a point is read off the norm of `L`. SURVIVED.
- **L6.6** `supSeminorm_eq_norm` — Q: [BGR] 5.1.4/6 `bgr-5.1.md:307–308` *"The Gauss norm `| |` and
  the supremum norm `| |_sup` coincide on `Tₙ`."* M: literal. D: L5.8, L6.4, `le_ciSup` with L5.7. A:
  [2] `σ` empty: `Tₙ = K`, one point, `|f|_sup = ‖f‖` ✓. [3] completeness of `K` necessary for L5.8.
  [5] three lemmas. SURVIVED.
- **L6.7** `eq_zero_of_forall_mem` — Q: [BGR] 5.1.4/5 `bgr-5.1.md:295–300` *"If `f ∈ Tₙ` vanishes for
  all `x ∈ Bⁿ(k_a)`, then `f = 0`. … Proof. If `f` induces the zero function, then
  `|f| = sup_{x∈Bⁿ(k_a)} |f(x)| = 0` and hence `f = 0`."* M: on the maximal spectrum. D: L6.4, L5.2,
  `norm_eq_zero`. A: [4] this is also L2.20 (`jacobson ⊥ = ⊥`) — two proofs of the same fact; L2.20
  holds for every `σ` and is the one the Jacobson property uses, L6.7 is the function-theoretic form
  [RM] §0.1.4 asks for; both kept. SURVIVED.

### Internal nodes

- **N6** the replacement of BGR's Lemma 3.4.1/4 by L6.1–L6.2. [6] composition: L6.3 needs a finite
  `S ⊆ L⁰` with `‖s − t‖ = 1`, of cardinality exceeding finitely many exponents; L6.1 gives `m`, L6.2
  gives `S` in a field that is complete for a norm extending that of `K` ✓. [4] **deviation from the
  source's lemma chain, declared**: BGR cites 3.4.1/4, whose proof (continuity of roots, 3.4.1/1–3,
  `bgr-3.2.md:81–93`) is about `k_a`; formalising it would require the valued field `k_a` and still
  end in a finite subextension. L6.2 is its content for one polynomial, with a complete proof above
  from Mathlib lemmas that exist. [1] the red-flag test of the planning rules — "substantial new
  infrastructure" or "a false leaf" — fails on both counts: two leaves, no new definition, both
  verified by hand at `m = 1, 2` and in characteristic `p`. SURVIVED; flagged to the user in
  `plan.md`.

---

## G7 — Distinguished series and Weierstrass polynomials (`TateAlgebra/Distinguished.lean`), [RM] §0.2.1

### Source and prose proof

[BGR] 5.2.1/1 (`bgr-5.2.md:29–38`): *"A strictly convergent power series
`g = Σ_{ν=0}^∞ g_ν(X₁, …, X_{n−1}) Xₙ^ν` is `Xₙ`-distinguished of degree `s` if (1) `g_s` is a unit
in `T_{n−1}` and (2) `|g_s| = |g|` and `|g_s| > |g_ν|` for all `ν > s`. It is easy to see that a power
series `g ∈ Tₙ` with `|g| = 1` is `Xₙ`-distinguished of degree `s` if and only if `g̃ ∈ T̃ₙ` is a
unitary polynomial of degree `s` in the polynomial ring `k̃[X₁, …, X_{n−1}][Xₙ]`. (Recall that a
polynomial is called unitary if its highest coefficient is a unit, and use Proposition 5.1.3/1.)"*
[BGR] 5.2.3/1–2 (`bgr-5.2.md:122–131`): *"A Weierstrass polynomial (in `Xₙ`) is a monic polynomial
`ω ∈ T_{n−1}[Xₙ]` with `|ω| = 1`. … **Lemma 2.** Let `ω₁` and `ω₂` be monic polynomials in
`T_{n−1}[Xₙ]`. If `ω₁·ω₂` is a Weierstrass polynomial, then `ω₁` and `ω₂` are Weierstrass polynomials.
Proof. Since `ω₁` and `ω₂` are monic, we have `|ωᵢ| ≥ 1` for `i = 1, 2`. On the other hand,
`|ω₁| |ω₂| = |ω₁·ω₂| = 1`, and therefore we get `|ωᵢ| = 1`."* [BGR] 5.2.2/1 (`bgr-5.2.md:96–99`):
*"Let `g ∈ Tₙ` be `Xₙ`-distinguished of degree `s`. Then there are a unique monic polynomial
`ω ∈ T_{n−1}[Xₙ]` of degree `s` and a unique unit `e ∈ Tₙ` such that `g = e·ω`. One has: `|ω| = 1`
so that `ω` is `Xₙ`-distinguished of degree `s`."*

The distinguished variable on the board is `X 0`, the variable Mathlib's `finSuccEquiv` splits off
(BGR and Bosch use the last one). [TOWER] gives the coefficients `coeffX0 g ν ∈ Tₙ` of
`g ∈ T_{n+1}`, the polynomials `ofPolynomial`, the definition of distinguishedness in BGR's form
(`isMulDistinguishedX0_iff`) and Weierstrass division and preparation. This file adds the dictionary:
`coeffX0` is additive and `K`-linear; the Gauss norm of `g` is the maximum of the Gauss norms of the
`g_ν` (each coefficient of `g` is a coefficient of some `g_ν` and conversely), and they tend to zero;
`ofPolynomial` and `ofTail` send variables and constants where they should, and are isometric on
coefficients. Distinguishedness is invariant under nonzero scalars; order `0` means unit (Bosch);
for norm one it is read off the reduction (BGR's remark, through G2). A Weierstrass polynomial is
BGR's 5.2.3/1 — ⚠ [RM] §0.2.1 says "all non-leading coefficients of Gauss norm `< 1`", which is not
BGR's definition and is wrong: `X − 1` is distinguished of order one and is its own Weierstrass
polynomial (erratum E1). Lemma 2 and preparation in the form "unit times Weierstrass polynomial"
follow; uniqueness needs the two polynomials to have the same degree, which is read off the
reduction.

### Leaves

- **L7.1** `coeffX0_add`, **L7.2** `coeffX0_smul` — Q: [BGR] `bgr-5.1.md:24` *"In particular, we have
  `Tₙ(k) = Tₙ₋₁(k)⟨Xₙ⟩`"*. M: the coefficient maps of this identification are `K`-linear. D:
  `Restricted.ext`, `MvPowerSeries.ext`, [TOWER] `coeff_coeffX0`, `val_add`, `val_smul`,
  `MvPowerSeries.coeff_smul`. SURVIVED ([2] `ν` arbitrary ✓; [3] none; [5] the seam is crossed only
  through `coeff_coeffX0`).
- **L7.3** `norm_coeffX0_le`, **L7.4** `norm_le_iff_forall_norm_coeffX0_le` — Q: [BGR]
  `bgr-5.2.md:175` *"`max_{0≤ν≤s−1} |t_ν| = |Σ_{ν=0}^{s−1} t_ν Xₙ^ν|`"* (the Gauss norm of a series
  in `Xₙ` is the maximum of the norms of its coefficients). M: the general form: `‖g‖ ≤ ε` iff every
  `‖g_ν‖ ≤ ε`. D: L1.9, L1.11, `coeff_coeffX0`, `Finsupp.cons_tail`. A: [2] `g = 0` ✓. [4] the quote
  is for polynomials; the series case is the same computation on coefficients and is what
  `isMulDistinguishedX0_iff` (`‖g_s‖ = ‖g‖`) presupposes. [5] verified. SURVIVED.
- **L7.5** `tendsto_norm_coeffX0` — Q: [BGR] `bgr-5.1.md:24` (`Tₙ = Tₙ₋₁⟨Xₙ⟩`: the `g_ν` form a zero
  sequence). M: literal. D: L1.14 (finitely many large coefficients), L1.12, `Metric.tendsto_atTop`,
  `Finset.sup` of the first exponents. A: [5] the alternative through the floor's
  `(finSuccEquiv K 1 g).2` crosses the `Fin.tail` seam and is avoided on purpose (plan, seam rule).
  [2] `g = 0` ✓. [3] none. SURVIVED.
- **L7.6** `ofTail_injective` — Q: [BGR] `bgr-5.2.md:186–187` *"the `k`-algebra monomorphism
  `T_{n−1} ↪ Tₙ/ωTₙ` induced by the natural injection `T_{n−1} ↪ Tₙ`"*. M: the natural injection is
  injective. D: [TOWER] `ofPolynomial_injective`, `Polynomial.C_injective`. SURVIVED.
- **L7.7** `ofPolynomial_X`, **L7.8** `ofTail_X`, **L7.9** `ofTail_C` — Q: [BGR] `bgr-5.2.md:144–147`
  *"`T_{n−1}^s ──j──→ T_{n−1}[Xₙ] ──i──→ Tₙ` … where `i` is the natural injection"*. M: the natural
  injection sends the variable to `X 0`, the variables of `Tₙ` to the later variables, constants to
  constants. D: `Restricted.ext`, `MvPowerSeries.ext`, [TOWER] `coeff_ofPolynomial`,
  `MvPowerSeries.coeff_X`, `coeff_C`, `Polynomial.coeff_X`, `Polynomial.coeff_C`, and the index
  facts `t = Finsupp.cons (t 0) (Finsupp.tail t)`. A: [2] `n = 0`: `ofTail_X` is vacuous (`Fin 0`),
  `ofPolynomial_X` and `ofTail_C` hold ✓. [5] each is a coefficient comparison with one index
  lemma; tagged `@[simp]`. SURVIVED.
- **L7.10** `norm_ofPolynomial_le_iff`, **L7.11** `norm_ofTail` — Q: as L7.3–L7.4 (`bgr-5.2.md:175`).
  M: literal for polynomials; `ofTail` is isometric. D: L7.4, [TOWER] `coeffX0_ofPolynomial`.
  SURVIVED ([2] `p = 0` ✓; [5] two lemmas).
- **L7.12** `ne_zero_of_isMulDistinguishedX0` — Q: [BGR] `bgr-5.2.md:32` *"(1) `g_s` is a unit in
  `T_{n−1}`"*. M: so `g ≠ 0`. D: [TOWER] `isMulDistinguishedX0_iff`, `not_isUnit_zero`, L1.3.
  SURVIVED ([2] `n = 0` ✓).
- **L7.13** `isMulDistinguishedX0_smul_iff` — Q: [BGR] `bgr-5.2.md:57` *"Without loss of generality,
  we may assume `|g| = 1`"* (distinguishedness is unchanged by a nonzero scalar). M: literal. D:
  `isMulDistinguishedX0_iff`, L7.2, L1.8, `Algebra.smul_def` and `IsUnit.mul_iff`. A: [1] `a = 0`
  makes the left side false and the right possibly true — `a ≠ 0` necessary ✓. [5] verified.
  SURVIVED.
- **L7.14** `isMulDistinguishedX0_zero_iff` — Q: [Bo] `bosch-lectures.txt:477–478` *"Thereby we see
  that an arbitrary series `g ∈ Tₙ` is `ζₙ`-distinguished of order `0` if and only if it is a
  unit."* M: literal. D: `isMulDistinguishedX0_iff`, L2.16 for `g` and for `g₀`, `coeff_coeffX0`,
  L1.12. A: [2] `n = 0` (`T₁`): `g₀` a nonzero constant dominating the rest ✓. [3] completeness
  needed in both directions (L2.16). [5] the two directions are coefficient comparisons through
  `Finsupp.cons`. SURVIVED.
- **L7.15** `coeff_finSuccEquiv_reduction` — Q: [BGR] `bgr-5.2.md:36–37` *"in the polynomial ring
  `k̃[X₁, …, X_{n−1}][Xₙ]`"*. M: the `ν`-th coefficient of the reduction, read as a polynomial in
  `X 0`, is the reduction of `g_ν`. D: `MvPolynomial.ext`, `MvPolynomial.finSuccEquiv_coeff_coeff`,
  L2 `coeff_reduction`, `coeff_coeffX0`. SURVIVED ([2] `ν` beyond the degree: both `0` ✓; [5]
  verified).
- **L7.16** `isMulDistinguishedX0_iff_reduction` — Q: [BGR] `bgr-5.2.md:35–38` (quoted above). M:
  "unitary polynomial of degree `s`" is `natDegree = s ∧ IsUnit leadingCoeff`. D: L7.15, L2.6, L2.7,
  L2.18, `Polynomial.natDegree_le_iff_coeff_eq_zero`, `Polynomial.coeff_eq_zero_of_natDegree_lt`. A:
  [1] junk: if the reduction were `0`, `natDegree = 0` and `leadingCoeff = 0` is not a unit, so the
  right side is false, and the left side is false too (`‖g‖ = 1` forces a nonzero reduction) ✓. [2]
  `s = 0`: units ✓ (L7.14). [3] `‖g‖ = 1` necessary (the reduction of `p·g` is `0`); completeness
  necessary for L2.18. [4] exact. SURVIVED.
- **L7.17** `isWeierstrassPolynomial_iff` — Q: [BGR] 5.2.3/1 `bgr-5.2.md:122–123`. M: for a monic
  polynomial, `|ω| = 1` iff all coefficients have norm `≤ 1`. D: L7.10; the leading coefficient `1`
  gives `1 ≤ ‖ofPolynomial ω‖` (L7.3, `coeffX0_ofPolynomial`, `norm_one`). A: [1] `ω = X − 1`: a
  Weierstrass polynomial, with a non-leading coefficient of norm one — the roadmap's definition
  would exclude it (erratum E1) ✓. [2] `ω = 1` ✓. [5] verified. SURVIVED.
- **L7.18** `isWeierstrassPolynomial_X_pow` — Q: [BGR] `bgr-5.2.md:102–103` *"`Xₙ^s = e′g + r′`.
  Define `ω := Xₙ^s − r′`"* (`Xₙ^s` is the model). M: `X^s` is a Weierstrass polynomial. D: L7.17,
  `Polynomial.monic_X_pow`, `Polynomial.coeff_X_pow`. SURVIVED.
- **L7.19** `IsWeierstrassPolynomial.of_mul_left`, **L7.20** `…of_mul_right` — Q: [BGR] 5.2.3/2
  `bgr-5.2.md:127–131` (quoted above). M: the two halves of the lemma. D: `map_mul`, `norm_mul`
  (floor `NormMulClass`), `1 ≤ ‖ofPolynomial ωᵢ‖` as in L7.17, `Polynomial.Monic.mul`. A: [1]
  monicity of the factors is necessary: `(p X) · (p⁻¹ X) = X²` is a Weierstrass polynomial and
  neither factor is one ✓. [3] no completeness. [5] the assembly `of_mul` is complete
  in the skeleton. SURVIVED.
- **L7.21** `IsWeierstrassPolynomial.isMulDistinguishedX0` — Q: [BGR] `bgr-5.2.md:98–99` *"`|ω| = 1`
  so that `ω` is `Xₙ`-distinguished of degree `s`"*. M: literal, of order `natDegree ω`. D:
  `isMulDistinguishedX0_iff`, `coeffX0_ofPolynomial`, `Polynomial.Monic.coeff_natDegree`,
  `Polynomial.coeff_eq_zero_of_natDegree_lt`, `isUnit_one`. SURVIVED ([2] `ω = 1`: order `0` ✓; [3]
  no completeness).
- **L7.22** `exists_isWeierstrassPolynomial_of_isMulDistinguishedX0` — Q: [BGR] `bgr-5.2.md:133–134`
  *"for every `Xₙ`-distinguished power series `g`, there is a Weierstrass polynomial `ω` with
  `ωTₙ = gTₙ`"*; 5.2.2/1. M: `g = e · ω` with `e` a unit (bundled as `(TateAlgebra K (n+1))ˣ`) and
  `natDegree ω = s`. D: [TOWER] `weierstrassPreparation_exists`,
  `Polynomial.natDegree_eq_of_degree_eq_some`. SURVIVED.
- **L7.23** `IsWeierstrassPolynomial.eq_of_mul_eq_mul` — Q: [BGR] `bgr-5.2.md:112–114` *"Now let
  `ω ∈ T_{n−1}[Xₙ]` be a monic polynomial of degree `s` and `e` be a unit in `Tₙ` such that
  `g = e·ω`. Define `r := Xₙ^s − ω`. Then one has `Xₙ^s = e⁻¹g + r`. The series `g` being given, this
  relation uniquely determines `e` and `r`, and therefore also `ω`."* M: two Weierstrass polynomials
  that differ by a unit are equal. D: the degrees agree: both `ofPolynomial ωᵢ` are distinguished of
  order `natDegree ωᵢ` (L7.21) with norm one, the unit has norm one and reduces to a unit, so the two
  reductions have the same degree in `X 0` (L7.16, `Polynomial.natDegree_mul`,
  `Polynomial.natDegree_eq_zero_of_isUnit`); then [TOWER] `weierstrassPreparation_omega_unique`. A:
  [1] could the degrees differ? Not after the reduction argument; without it BGR's uniqueness is only
  "for a given degree `s`" — the leaf is stronger than the quote and the extra step is declared.
  [3] `[CompleteSpace K]` (defect D3). [5] alternative: Euclidean division of `ω₁` by `ω₂` and the
  floor's `weierstrassDivision_polynomial_of_isMulDistinguishedX0`. SURVIVED.

### Internal node

- **N7** the structure `IsWeierstrassPolynomial` (complete in the skeleton: `monic`, `norm_eq_one`)
  — source [BGR] 5.2.3/1, verbatim. [6] L7.17 shows the two-field structure is equivalent to the
  coefficientwise form used in the examples; nothing else is defined in this file. SURVIVED.

---

## G8 — The Weierstrass finiteness theorem (`TateAlgebra/Finiteness.lean`), [RM] §0.2.2

### Source and prose proof

[BGR] 5.2.3/3–4 (`bgr-5.2.md:137–140`, `:164–167`, `:183–187`, `:197–201`): *"Let `ω` be a Weierstrass
polynomial of degree `s` in `Xₙ`. Then (i) `Tₙ/ωTₙ` is a finite free `T_{n−1}`-module; (ii)
`T_{n−1}[Xₙ]/ωT_{n−1}[Xₙ] ≅ Tₙ/ωTₙ`. … The existence statement of the WEIERSTRASS Division Theorem
tells us that `π∘i∘j` and `ψ∘j` are surjective. Hence `ī` and `j̄` must be surjective. Furthermore,
the uniqueness part of the Division Theorem shows that `π∘i∘j` is injective, whence the injectivity
of `j̄` and `ī` follows. … **Theorem 4.** Let `A` be a `k`-Banach algebra, let `φ : Tₙ → A` be a
finite `k`-algebra homomorphism and let `ω ∈ T_{n−1}[Xₙ]` be a Weierstrass polynomial contained in
`ker φ`. Then the map `φ′ : T_{n−1} → A` defined by `φ′ := φ | T_{n−1}` is also finite. … Since `φ`
is finite, so is `φ̄`. By the preceding proposition, `Tₙ/ωTₙ` is a finite `T_{n−1}`-module via `ε̄`;
i.e., the map `ε̄` is finite. Then `φ̄∘ε̄` is also finite. Since `φ′ = φ∘ε = φ̄∘ε̄`, the proof is
finished."*

A Weierstrass polynomial is distinguished of order its degree (L7.21), so division by it exists and
is unique ([TOWER]); "`π∘i∘j` bijective" is the statement that every class modulo `ω` has exactly one
representative of degree `< s`. The natural map `Tₙ[X]/(ω) → T_{n+1}/(ω)` is then surjective by
existence and injective by uniqueness applied to the Euclidean remainder. Finiteness of
`Tₙ → T_{n+1}/(ω)` follows from the finiteness of `Tₙ → Tₙ[X]/(ω)` (a monic polynomial) and the
bijection. Theorem 4 is BGR's factorisation `φ′ = φ̄ ∘ ε̄`; the isometry part of 5.2.3/3 is not
needed in Layer 0 and is not stated.

### Leaves

- **L8.1** `IsWeierstrassPolynomial.existsUnique_remainder` — Q: [BGR] 5.2.3/3 (i) and
  `bgr-5.2.md:164–166` (quoted above). M: "`π∘i∘j` is bijective": a unique `r` of degree `< deg ω`
  with `f − r ∈ (ω)`. D: L7.21, [TOWER] `weierstrassDivision_exists`, `weierstrassDivision_r_unique`,
  `Ideal.mem_span_singleton'`, `Polynomial.degree_eq_natDegree`. A: [2] `ω = 1`: `r = 0`, the ideal
  is everything ✓. [3] completeness needed for existence. [4] freeness of rank `s` is this statement;
  it is not restated as `Module.Free`. SURVIVED.
- **L8.2** `IsWeierstrassPolynomial.bijective_quotientMap` — Q: [BGR] 5.2.3/3 (ii)
  `bgr-5.2.md:140`. M: the natural map of quotients is bijective, in the exact shape of axiom (2) of
  `IsRueckert`. D: surjectivity from L8.1 (existence); injectivity from
  `injective_iff_map_eq_zero`, `Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`,
  L8.1 (uniqueness, applied to the remainder and to `0`), `Ideal.map_span`, `Set.image_singleton`.
  A: [1] is the map well defined? `Ideal.quotientMap` with `Ideal.le_comap_map` ✓ (compiles). [2]
  `ω = 1`: both quotients trivial ✓. [5] verified. SURVIVED.
- **L8.3** `IsWeierstrassPolynomial.finite_mk_comp_ofTail` — Q: [BGR] `bgr-5.2.md:185–187` *"In
  particular, the `k`-algebra monomorphism `T_{n−1} ↪ Tₙ/ωTₙ` induced by the natural injection
  `T_{n−1} ↪ Tₙ` is finite for every Weierstrass polynomial `ω`."* M: literal. D:
  `Polynomial.Monic.finite_quotient`, `RingHom.Finite.of_surjective` (L8.2), `RingHom.Finite.comp`,
  `Ideal.quotEquivOfEq` between the two spellings of the ideal. A: [2] `ω = 1` ✓. [5] the Mathlib
  lemma is `g.Monic → Module.Finite R (R[X] ⧸ Ideal.span {g})` (`names_mathlib4.out`). SURVIVED.
- **L8.4** `IsWeierstrassPolynomial.injective_mk_comp_ofTail` — Q: as L8.3 (*"monomorphism"*). M:
  injective when `0 < natDegree ω`. D: L8.1 (uniqueness for `ofTail a`), `Polynomial.degree_C_le`.
  A: [1] `ω = 1`: the target is the zero ring and the map is not injective — the degree hypothesis
  is necessary, and BGR's "monomorphism" silently assumes `s > 0` ✓ declared. SURVIVED.
- **L8.5** `IsWeierstrassPolynomial.finite_comp_ofTail` — Q: [BGR] 5.2.3/4 (quoted above). M:
  literal, for any commutative ring `A` (the Banach structure of `A` is not used by BGR's proof).
  D: `Ideal.Quotient.lift`, `RingHom.Finite.of_comp_finite`, L8.3, `RingHom.Finite.comp`. SURVIVED
  ([3] `A` need not be a `K`-algebra; [5] verified).
- **L8.6** `finite_mk_comp_ofTail_of_isMulDistinguishedX0` — Q: [Bo] `bosch-lectures.txt:620–622`
  *"By Weierstraß division we know that any `f ∈ Tₙ` is congruent modulo `g` to a polynomial
  `r ∈ T_{n−1}[ζₙ]` of degree `< s`. In other words, the canonical morphism `T_{n−1} → Tₙ → Tₙ/(g)` is
  finite"*. M: literal. D: L7.22, L8.5 with `φ := Ideal.Quotient.mk (span {g})`
  (`RingHom.Finite.of_surjective`). SURVIVED.
- **L8.7** `IsWeierstrassPolynomial.finite_compHom` — Q: [RM] §0.2.2 *"State the module version: for
  a finite `Tₙ`-module `M` killed by `ω`, `M` is a finite `T_{n−1}`-module."* M: literal, with the
  `Tₙ`-module structure `Module.compHom M (ofTail K n)`. D: generators `X 0 ^ i • m_j` (`i < s`) of
  `M` over `Tₙ`, from L8.1 (existence) and `Polynomial.as_sum_range'`. A: [2] `M = 0` ✓. [4] BGR
  states the homomorphism form only; the module form is the roadmap's and is the same proof. [5] the
  explicit-generators proof avoids the instance juggling of `Module.Finite.trans`. SURVIVED.

---

## G9 — Distinguished charts (`TateAlgebra/Chart.lean`), [RM] §0.2.3

### Source and prose proof

[BGR] 5.1.3, Example (`bgr-5.1.md:198–204`): *"Let `c₁, …, c_{n−1} ∈ ℕ` be given. Define
`φ : Tₙ → Tₙ` by `φ(X_ν) := X_ν + Xₙ^{c_ν}` for `ν = 1, …, n − 1` and `φ(Xₙ) := Xₙ`. Then `φ` is an
isometric automorphism of `Tₙ`. Proof. Let `ψ : Tₙ → Tₙ` be defined by `ψ(X_ν) := X_ν − Xₙ^{c_ν}` …
One easily checks that `ψ` is an inverse of `φ`."* [Bo] 1.2/7 (`bosch-lectures.txt:496–528`): *"As
`|σ(f)| ≤ |f|` for all `f ∈ Tₙ` and a similar estimate holds for `σ⁻¹`, we have, in fact,
`|σ(f)| = |f|` for all `f ∈ Tₙ`. … Now choose `t` greater than the maximum of all `νᵢ` occurring as a
component of some `ν ∈ N`, and consider the automorphism `σ` of `Tₙ` obtained from
`α₁ = t^{n−1}, …, α_{n−1} = t`. Its reduction `σ̃` on `k[ζ₁, …, ζₙ]` satisfies
`σ̃(f̃) = Σ_{ν∈N} c̃_ν ζₙ^{α₁ν₁+…+α_{n−1}ν_{n−1}+νₙ} + g̃`, where `g̃ ∈ k[ζ₁, …, ζₙ]` is a polynomial
whose degree in `ζₙ` is strictly less than the maximum of all exponents `α₁ν₁ + … + α_{n−1}ν_{n−1} + νₙ`
with `ν` varying over `N`. Due to the choice of `α₁, …, α_{n−1}`, these exponents are pairwise
different and, hence, their maximum `s` is assumed at a single index `ν ∈ N`. But then
`σ̃(f̃) = c̃_ν ζₙ^s +` a polynomial of degree `< s` in `ζₙ`. As `c̃_ν ≠ 0`, it follows that `σ(f)` is
`ζₙ`-distinguished of order `s`."* [BGR] 5.2.4/2 (`bgr-5.2.md:258–264`) is the same statement with
`t ≥ max μᵢ` over the indices with `|a_μ| = |f|`.

With `X 0` distinguished, the shear is `X 0 ↦ X 0`, `X (i+1) ↦ X (i+1) + X 0 ^ (e i)`, and the
exponents are `e i = t^{i+1}` for `t` *exceeding* every exponent of a coefficient of maximal norm
(Bosch's convention; BGR's `t` is one less, with `cᵢ = (1+t)^{n−i}`). The polynomial statement is
proved first, over the residue field: the shear of a monomial `X^v` has degree
`D(v) = v 0 + Σ t^{i+1} v (i+1) = Σ_j t^j v j` in `X 0` and leading coefficient `1` (for positive
exponents); `D` is injective on exponent vectors with entries `< t` (uniqueness of base-`t`
expansions); so the monomial maximising `D` contributes the leading coefficient, a nonzero constant.
On the Tate algebra the shear is the substitution homomorphism of G3; it is an automorphism because
it and its inverse compose to continuous homomorphisms fixing the variables (L3.19), and an isometry
because both are contractive; its reduction is the polynomial shear (L4.4); and distinguishedness of
`σ(f)` for `‖f‖ = 1` is the criterion L7.16. ⚠ [RM] §0.2.3 also asks for a relative form over an
affinoid base (Bosch 1.8/13); that statement is about `A⟨ζ⟩` and `Sp A`, which are Layers 1 and 3,
and is moved to Layer 4 where it is consumed (erratum E8). The explicit form L9.14 and the
finitely-many form L9.16 are what Layer 0 can state.

### Leaves

- **L9.1** `MvPolynomial.shearAlgHom_comp_shearAlgHom` — Q: [BGR] `bgr-5.1.md:202–203` *"One easily
  checks that `ψ` is an inverse of `φ`"*, on reductions. M: the shears with parameters `a`, `b`,
  `a + b = 0`, compose to the identity. D: `MvPolynomial.algHom_ext`, `MvPolynomial.aeval_X`,
  `Fin.cases`, `map_add`, `map_mul`, `map_pow`, `MvPolynomial.aeval_C`. SURVIVED ([2] `n = 0` ✓; [3]
  any commutative ring; [5] verified).
- **L9.2** `MvPolynomial.shear_X_zero`, **L9.3** `MvPolynomial.shear_X_succ` — Q: [BGR]
  `bgr-5.1.md:199` *"`φ(X_ν) := X_ν + Xₙ^{c_ν}` … and `φ(Xₙ) := Xₙ`"*. M: literal. D:
  `MvPolynomial.aeval_X`, `Fin.cases_zero`, `Fin.cases_succ`, `map_one`, `one_mul`. SURVIVED.
- **L9.4** `MvPolynomial.sum_pow_mul_ne_of_lt` — Q: [Bo] `bosch-lectures.txt:524–525` *"Due to the
  choice of `α₁, …, α_{n−1}`, these exponents are pairwise different"*. M: `v ↦ Σ_j t^j v j` is
  injective on vectors with entries `< t`. D: induction on `n` with `Fin.sum_univ_succ`: reduce
  modulo `t` to get `v 0 = w 0`, cancel `t`. A: [1] entries `= t` break it (`(t, 0)` and `(0, 1)`):
  the strict bound is necessary ✓ — and this is why the board follows Bosch's strict `t` and not
  BGR's `t ≥ max`. [2] `n = 0` ✓; `t = 1`: all entries `0`, `v = w`, vacuous ✓. [5] alternative:
  `Nat.ofDigits_inj_of_len_eq` (verified). SURVIVED.
- **L9.5** `MvPolynomial.degreeOf_zero_shear_monomial` — Q: [Bo] `bosch-lectures.txt:513–517`
  (the exponent `α₁ν₁ + … + α_{n−1}ν_{n−1} + νₙ`). M: the degree in `X 0` of the shear of a
  monomial. D: `MvPolynomial.natDegree_finSuccEquiv`, `MvPolynomial.monomial_eq`,
  `Finsupp.prod_fintype`, `Fin.prod_univ_succ`, `finSuccEquiv_X_zero`, `finSuccEquiv_X_succ`,
  `Polynomial.natDegree_mul`, `natDegree_pow`, `Polynomial.natDegree_prod`,
  `Polynomial.natDegree_X_pow_add_C`. A: [1] `e i = 0`: the factor is `C (X i + 1)`, of degree
  `0 = e i` ✓ — the degree formula holds for every `e`. [3] `a ≠ 0` necessary (the zero polynomial
  has degree `0`). [5] the product formula for `finSuccEquiv (shear (monomial v a))` is a private
  lemma shared with L9.6. SURVIVED.
- **L9.6** `MvPolynomial.leadingCoeff_finSuccEquiv_shear_monomial` — Q: [Bo]
  `bosch-lectures.txt:526–527` *"`σ̃(f̃) = c̃_ν ζₙ^s +` a polynomial of degree `< s` in `ζₙ`"*. M: the
  leading coefficient of the shear of `a X^v` is the constant `a`. D: the product formula,
  `Polynomial.leadingCoeff_mul`, `leadingCoeff_pow`, `Polynomial.leadingCoeff_prod`,
  `Polynomial.leadingCoeff_X_pow_add_C`. A: [1] `e i = 0` is a counterexample to the statement
  without `he` (defect D1); with `he` none. [2] `a = 0`: both sides `0` ✓ (no `a ≠ 0` needed). [5]
  verified. SURVIVED.
- **L9.7** `MvPolynomial.isUnit_leadingCoeff_finSuccEquiv_shear` — Q: [Bo]
  `bosch-lectures.txt:524–528` (quoted above). M: literal: for `t` exceeding every exponent of
  `f ≠ 0`, the leading coefficient in `X 0` of the shear with exponents `t^{i+1}` is a unit. D:
  `MvPolynomial.as_sum`, `Finset.exists_max_image`, L9.4, L9.5, L9.6,
  `Finset.sum_eq_add_sum_sdiff_singleton_of_mem`, `Polynomial.degree_sum_le`,
  `Polynomial.leadingCoeff_add_of_degree_lt`. A: [2] one monomial ✓; `n = 0`: the leading
  coefficient of a nonzero one-variable polynomial ✓. [3] a field is used for "nonzero constant is a
  unit". [4] exact (Bosch). SURVIVED.
- **L9.8** `norm_shearTuple_le_one` — Q: [BGR] `bgr-5.1.md:149–150` *"According to the theorem, we
  have `|fᵢ| ≤ |Xᵢ| = 1`, whence `fᵢ ∈ T̊ₘ`"*. M: the images of the variables are power-bounded. D:
  [SEAM] `norm_X`, `norm_C`, `IsUltrametricDist.norm_add_le_max`, `norm_mul_le`, `norm_pow_le`.
  SURVIVED ([3] `‖a‖ ≤ 1` necessary; no completeness, `omit`ted).
- **L9.9** `shearAlgHom_comp_shearAlgHom` (Tate algebra) — Q: [BGR] `bgr-5.1.md:202–203`. M: as
  L9.1. D: L3.19 with L3.18 for continuity; L3.15; `map_add`, `map_mul`, `map_pow`,
  `AlgHom.commutes`. SURVIVED ([5] the same computation as L9.1 after `aeval_X`).
- **L9.10** `shear_X_zero`, **L9.11** `shear_X_succ` (Tate algebra) — Q: `bgr-5.1.md:199`. D: L3.15.
  SURVIVED.
- **L9.12** `norm_shear` — Q: [Bo] `bosch-lectures.txt:496–497` *"As `|σ(f)| ≤ |f|` for all `f ∈ Tₙ`
  and a similar estimate holds for `σ⁻¹`, we have, in fact, `|σ(f)| = |f|`"*. M: literal. D: L3.17
  twice, `AlgEquiv.symm_apply_apply`. A: [4] BGR derives the isometry from 5.1.3/6 (every isomorphism
  is an isometry, via 5.1.3/4); Bosch's two-sided contraction is the route taken and needs no
  5.1.3/4. SURVIVED.
- **L9.13** `reduction_shear` — Q: [BGR] `bgr-5.2.md:244` *"`(σ(f))~ = σ̃(f̃)`"*. M: literal. D: L4.4
  with the tuple `shearTuple K n e 1`, and the reductions of the variables (a private lemma
  `reduction_X`). SURVIVED ([5] the membership proofs in the two statements differ only by proof
  irrelevance).
- **L9.14** `exists_isMulDistinguishedX0_shear` — Q: [BGR] 5.2.4/2 `bgr-5.2.md:258–264` and [Bo]
  1.2/7. M: for `t` exceeding every exponent at a coefficient of maximal norm, the shear with
  exponents `t^{i+1}` makes `f` distinguished. D: L1.16, L7.13 (scaling), L2.1 and L2.7 for the
  support of the reduction, L9.7, L9.13, L9.12, L7.16. A: [1] BGR's `t ≥ max` with exponents
  `(1+t)^j` and the board's `t > max` with exponents `t^j` are the same family ✓. [2] `n = 0` ✓. [3]
  `f ≠ 0` necessary. [4] the order `s` is not stated (BGR gives a formula); the consumers need only
  its existence. SURVIVED.
- **L9.15** `exists_shear_isMulDistinguishedX0` — Q: [BGR] 5.2.4/1 `bgr-5.2.md:219–220` *"For every
  `f ∈ Tₙ`, `f ≠ 0`, there is a `k`-algebra automorphism `σ` of `Tₙ` such that `σ(f)` is
  `Xₙ`-distinguished."* M: literal. D: L9.14 with `t` := one more than the supremum of the exponents
  over the finite set of L1.14. SURVIVED.
- **L9.16** `exists_shear_forall_isMulDistinguishedX0` — Q: [Bo] 1.2/7 `bosch-lectures.txt:479–487`
  *"Given finitely many non-zero elements `f₁, …, f_r ∈ Tₙ`, there is a continuous automorphism … such
  that the elements `σ(f₁), …, σ(f_r)` are `ζₙ`-distinguished"* and `:529–531` *"One just has to
  choose `t` big enough such that it works for all `fᵢ` simultaneously."* M: literal. D: L9.14 with a
  common `t`. SURVIVED ([2] `F = ∅` ✓).

### Internal node

- **N9** `MvPolynomial.shear`, `Affinoid.TateAlgebra.shear` (complete in the skeleton via
  `AlgEquiv.ofAlgHom` from L9.1, L9.9) — source [BGR] 5.1.3 Example. [6] the two composites are L9.1
  / L9.9 at `(1, −1)` and `(−1, 1)` ✓. [4] BGR's Example allows any exponents `c_ν`, as does the
  definition. SURVIVED.

---

## G10 — Rückert overrings (`Rueckert.lean`), [RM] §0.3.2–§0.3.4

### Source and prose proof

[BGR] 5.2.5/1 (`bgr-5.2.md:272–287`): *"Let `I` be a ring (commutative with identity element). An
overring `I′` of `I[X]` is called Rückert over `I` if there is a family `W` of monic polynomials in
`I[X]` such that the following three axioms are fulfilled: (1) If the product of two monic polynomials
lies in `W`, so do the factors. (2) For all `ω ∈ W`, there is an isomorphism of `I`-algebras
`I′/ωI′ ≅ I[X]/ωI[X]`. In particular, the canonical map `I → I′/ωI′` is finite. (3) For all
`f ∈ I′ − {0}`, there is an automorphism `σ` of `I′` and a unit `e` of `I′` such that `e·σ(f) ∈ W`.
… With respect to many aspects, a Rückert overring of `I` behaves as `I[X]` does."* The three
inheritance propositions are 5.2.5/2–4 (`bgr-5.2.md:291–364`), quoted at the leaves. For the
dimension, [BGR] 6.1.2, Remark (`bgr-6.1.2.md:49–57`): *"Namely, `dim A = dim T_d` (for example, use
NAGATA [28] Corollary 10.10), and `dim T_d = d`. The latter assertion is easily verified. Namely, the
chain of prime ideals `0 ⊂ (X₁) ⊂ (X₁, X₂) ⊂ … ⊂ (X₁, …, X_d)` shows that `dim T_d ≥ d`. Since each
maximal ideal in `T_d` can be generated by `d` elements (Proposition 7.1.1/3), we must have
`dim T_d = d`."* and [Bo] 1.2/10 (`bosch-lectures.txt:620–632`): *"the canonical morphism
`T_{n−1} → Tₙ → Tₙ/(g)` is finite … That `d` equals the Krull dimension of `Tₙ/a` follows from
commutative algebra."*

`IsRueckert φ W` is BGR's definition for a ring homomorphism `φ : I[X] →+* I′` (injective, since `I′`
is an "overring"), with axiom (2) in the form "the natural map `I[X]/(ω) → I′/(ω)` is bijective" —
the form BGR proves for `Tₙ` (5.2.3/3 (ii)) and uses in 5.2.5/4. The noetherian and factorial
propositions are BGR's proofs. For the Jacobson property BGR's element chase (an integral equation of
minimal degree, lying over) is Mathlib's `isJacobsonRing_of_isIntegral'`, applied to the finite map
`I → I′/𝔭′` that BGR constructs. For the dimension, BGR's upper bound uses 7.1.1/3, which rests on
Noether normalisation and on the description of `Max Tₙ` (Layers 1 and 3; `bgr-7.1.1.md:49–52`), so
the board uses the argument Bosch points to: every prime that is not minimal contains, after an
automorphism, some `ω ∈ W`, so its quotient is a quotient of `I′/(ω)`, which is integral over `I`
(axiom (2)) and hence of dimension at most `dim I` (Nagata 10.10, in the half "integral maps do not
raise the dimension"); and a ring all of whose such quotients have dimension `≤ d` has dimension
`≤ d + 1`. The lower bound is BGR's chain, in the form `dim I′ ≥ dim I′/(X) + 1` for the nonzero
divisor `X` (erratum E5).

### Leaves

- **L10.1** `ringKrullDim_le_of_isIntegral` — Q: [BGR] `bgr-6.1.2.md:50–51` *"`dim A = dim T_d` (for
  example, use NAGATA [28] Corollary 10.10)"*. M: the inequality `dim S ≤ dim R` for an integral
  `R → S` (the half of Nagata's statement that needs no injectivity). D:
  `Order.krullDim_le_of_strictMono` for `PrimeSpectrum.comap`, strictly monotone by
  `Ideal.comap_lt_comap_of_integral_mem_sdiff` (incomparability). A: [1] is injectivity needed? No:
  `ℤ → ℤ/p` is integral and the dimension drops ✓ (the inequality is the right direction). [2]
  `S = 0`: `⊥ ≤ _` ✓. [3] Mathlib has no such lemma at the pin (searched
  `ringKrullDim_le_of_isIntegral`, `Algebra.IsIntegral.ringKrullDim`: none). [5] the Mathlib lemma
  needs `[Algebra R S]`, obtained by `f.toAlgebra`. SURVIVED.
- **L10.2** `ringKrullDim_le_add_one_of_forall_quotient_le` — Q: [BGR] `bgr-6.1.2.md:51–56` (the
  dimension as the supremum of the lengths of chains of primes: *"the chain of prime ideals … shows
  that `dim T_d ≥ d`"*). M: glue for the upper bound: if `dim R/𝔭 ≤ d` for every prime `𝔭` properly
  containing another prime, then `dim R ≤ d + 1`. D: `iSup_le` over `LTSeries`; for a series of
  length `ℓ + 1`, `Order.rev_index_le_coheight` at index `1`, `Order.coheight_eq_krullDim_Ici`,
  `ringKrullDim_quotient`, `PrimeSpectrum.mem_zeroLocus`, `LTSeries.strictMono`. A: [1] `d` negative
  (`⊥`) with `R` a field: `dim R = 0 ≤ ⊥ + 1 = ⊥` is false — hence `hd : 0 ≤ d` ✓ necessary. [2]
  `R = 0`: `⊥ ≤ d + 1` ✓; `R` a field: no pair `q < p`, conclusion `0 ≤ d + 1` from `hd` ✓. [3] the
  hypothesis quantifies over pairs `q < p`, which is exactly "`p` is not minimal in a chain". [5]
  ⚠ `Order.krullDim_le_iff` does not exist; the three lemmas cited were located in
  `Mathlib/Order/KrullDimension.lean` and verified. SURVIVED.
- **L10.3** `IsRueckert.finite_mk_comp_C` — Q: [BGR] `bgr-5.2.md:277–278` *"In particular, the
  canonical map `I → I′/ωI′` is finite."* M: literal. D: `Polynomial.Monic.finite_quotient`,
  `RingHom.Finite.of_surjective` (axiom (2)), `RingHom.Finite.comp`, `Ideal.quotientMap_comp_mk`.
  SURVIVED ([2] `ω = 1` ✓; [5] verified).
- **L10.4** `IsRueckert.exists_ringEquiv_mem_map` — Q: [BGR] `bgr-5.2.md:293–294` *"According to axiom
  (3), we may assume that `𝔞` contains a polynomial `ω ∈ W`."* M: the "we may assume" made explicit:
  after an automorphism `σ`, the ideal `σ(𝔞)` contains `φ ω`. D:
  `Submodule.exists_mem_ne_zero_of_ne_bot`, axiom (3), `Ideal.mem_map_of_mem`, `Ideal.mul_mem_left`.
  SURVIVED ([2] `𝔞 = ⊤` ✓; [3] `𝔞 ≠ ⊥` necessary).
- **L10.5** `IsRueckert.isNoetherianRing` — Q: [BGR] 5.2.5/2 `bgr-5.2.md:291–297` *"A Rückert overring
  `I′` of a Noetherian ring `I` is Noetherian. Proof. We have to show that every ideal `𝔞 ≠ (0)` in
  `I′` is finitely generated. According to axiom (3), we may assume that `𝔞` contains a polynomial
  `ω ∈ W`. Since `I` is Noetherian by assumption, so is `I[X]` by HILBERT's Basis Theorem. Because
  `I′/ωI′` is isomorphic to `I[X]/ωI[X]` due to axiom (2), the image of `𝔞` in `I′/ωI′` has a finite
  generating system. Pulling back that system to `𝔞` and adding `ω`, we get a finite generating
  system for `𝔞`."* M: literal. D: `isNoetherianRing_iff_ideal_fg`, L10.4,
  `Polynomial.isNoetherianRing`, `Ideal.Quotient.isNoetherianRing`, `RingEquiv.ofBijective`,
  `isNoetherianRing_of_ringEquiv`, `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective` ("pulling back
  and adding `ω`"), `Ideal.mk_ker`, `Ideal.map_of_equiv` to return from `σ(𝔞)` to `𝔞`. A: [2]
  `𝔞 = ⊥` is finitely generated ✓. [3] injectivity of `φ` is not used here. [5] ⚠
  `isNoetherian_of_tower` goes the wrong way for a module-level proof; the ideal-level lemma
  `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective` is the right one (verified). SURVIVED.
- **L10.6** `IsRueckert.jacobson_eq_radical` — Q: [BGR] 5.2.5/3 `bgr-5.2.md:306–314` *"Let `I` be a
  Jacobson ring, and let `I′` be a Rückert overring of `I`. Then `rad 𝔞 = j(𝔞)` for any non-zero
  ideal `𝔞 ⊂ I′`. Proof. Since the nilradical of any ideal `𝔞 ⊂ I′` equals the intersection of all
  prime ideals containing `𝔞` …, we have only to show `j(𝔭′) = 𝔭′` for any non-zero prime ideal
  `𝔭′ ⊂ I′`. … We may assume that `𝔭′` contains an element `ω ∈ W` so that by axiom (2) the
  canonical injection `I/𝔭 ↪ I′/𝔭′` is finite."* M: literal. D: `Ideal.radical_le_jacobson`,
  `Ideal.radical_eq_sInf`, `Ideal.jacobson_mono`; for a nonzero prime: L10.4,
  `Ideal.map_isPrime_of_equiv`, `Ideal.map_jacobson_of_bijective`, L10.3,
  `RingHom.Finite.to_isIntegral`, `Ideal.Quotient.factor`, `RingHom.isIntegral_of_surjective`,
  `RingHom.IsIntegral.trans`, `isJacobsonRing_of_isIntegral'`,
  `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`. A: [1] BGR's counterexample for `𝔞 = 0`
  (`bgr-5.2.md:302–304`: *"`I := k` and `I′ := k⟦X⟧` provide a counterexample"*) shows that `𝔞 ≠ ⊥`
  cannot be dropped ✓. [4] the last third of BGR's proof (minimal integral equation,
  `bgr-5.2.md:315–329`) is the content of Mathlib's lemma "an integral extension of a Jacobson ring is
  Jacobson"; the reduction steps before it are BGR's. [5] all names verified. SURVIVED.
- **L10.7** `IsRueckert.isJacobsonRing` — Q: [BGR] 5.2.6/3 `bgr-5.2.md:394–395` *"Proposition 5.1.3/3
  tells us that `j(Tₙ) = 0`. Therefore we can conclude from Proposition 5.2.5/3 that `Tₙ` is a
  Jacobson ring if `T_{n−1}` is."* M: the abstract form: `j(I′) = 0` and `I` Jacobson imply `I′`
  Jacobson. D: `isJacobsonRing_iff_prime_eq`, L10.6, `Ideal.IsPrime.radical`. SURVIVED ([1]
  `k⟦X⟧`: `j ≠ 0`, hypothesis fails ✓; [2] the prime `⊥` is the case `h0` covers).
- **L10.8** `IsRueckert.uniqueFactorizationMonoid` — Q: [BGR] 5.2.5/4 `bgr-5.2.md:336–364` *"Every
  integral domain `I′`, which is Rückert over a factorial ring `I`, is factorial itself. … We have to
  factor every non-unit `f ∈ I′ − {0}` into prime elements. Since automorphisms and units do not
  matter for that task, we may assume `f ∈ W ⊂ I[X]`. … Consequently, `f = p₁ … p_r` is a
  factorization of `f` in `I[X]`. It remains to be shown that all `pᵢ` are prime elements in `I′`.
  Since `p₁, …, p_r ∈ W` (axiom (1)), and since `I[X]/pᵢI[X] ≅ I′/pᵢI′` for all `i` (axiom (2)), it
  is enough to show that each `pᵢ` is a prime element in `I[X]`."* M: literal. D: BGR remarks that
  "the assertion is an easy consequence of the fact that `I[X]` is factorial if `I` is factorial"
  (`bgr-5.2.md:341–342`) — that fact is `Polynomial.uniqueFactorizationMonoid`, so the direct Gauss
  lemma argument is not repeated: `UniqueFactorizationMonoid.exists_prime_factors` in `I[X]`,
  normalise each factor to be monic (`Polynomial.Monic.isUnit_leadingCoeff_of_dvd`,
  `Polynomial.eq_of_monic_of_associated`), axiom (1) by induction over the multiset
  (`Polynomial.monic_multiset_prod_of_monic`), axiom (2) with `Ideal.span_singleton_prime` and
  `Ideal.Quotient.isDomain_iff_prime`, `MulEquiv.prime_iff` for `σ⁻¹`,
  `UniqueFactorizationMonoid.of_exists_prime_factors`. A: [2] `f` a unit: `ω = 1`, empty
  factorisation ✓. [3] `IsDomain I′` is BGR's hypothesis; injectivity of `φ` is used (`φ pᵢ ≠ 0`).
  [5] the heaviest leaf of the file — a ticket of its own. SURVIVED.
- **L10.9** `IsRueckert.ringKrullDim_quotient_le` — Q: [Bo] `bosch-lectures.txt:622` *"the canonical
  morphism `T_{n−1} → Tₙ → Tₙ/(g)` is finite"*, with Nagata 10.10 (`bgr-6.1.2.md:50–51`). M:
  `dim I′/(ω) ≤ dim I`. D: L10.3, `RingHom.Finite.to_isIntegral`, L10.1. SURVIVED.
- **L10.10** `IsRueckert.ringKrullDim_le` — Q: [Bo] `bosch-lectures.txt:631–632` *"That `d` equals the
  Krull dimension of `Tₙ/a` follows from commutative algebra."* M: `dim I′ ≤ dim I + 1`. D: L10.2
  with `d = dim I`; for a non-minimal prime `𝔭`: L10.4, `Ideal.quotientEquiv` and
  `ringKrullDim_eq_of_ringEquiv` to pass to `σ(𝔭)`, `Ideal.Quotient.factor` and
  `ringKrullDim_le_of_surjective`, L10.9. A: [2] `I = 0`: then `I′ = 0` (`φ 1 = 1 = 0`),
  `⊥ ≤ ⊥ + 1` ✓ — a case split on `Subsingleton I`, since `hd` needs `0 ≤ dim I`
  (`ringKrullDim_nonneg_of_nontrivial`). [4] replaces BGR's 7.1.1/3 (erratum E5). SURVIVED.
- **L10.11** `IsRueckert.ringKrullDim_add_one_le` — Q: [BGR] `bgr-6.1.2.md:51–56` *"the chain of prime
  ideals `0 ⊂ (X₁) ⊂ (X₁, X₂) ⊂ … ⊂ (X₁, …, X_d)` shows that `dim T_d ≥ d`"*. M: one step of the
  chain: if `X ∈ W` and `I′` is a domain then `dim I + 1 ≤ dim I′`. D: axiom (2) for `ω = X`,
  `Polynomial.quotientSpanXSubCAlgEquiv` at `0`, `ringKrullDim_eq_of_ringEquiv`,
  `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, `Ideal.map_span`. A: [1] without `IsDomain I′`
  the element `φ X` need not be a nonzero divisor — hypothesis kept ✓. [2] `I` a field: `1 ≤ dim I′`
  ✓ (`(φ X)` is a nonzero prime). [3] `X ∈ W` holds for the Weierstrass family (L7.18). SURVIVED.

### Internal nodes

- **N10a** the structure `IsRueckert` (complete in the skeleton) — source [BGR] 5.2.5/1. [6] is the
  Lean axiom (2) BGR's? BGR asks for *an* isomorphism of `I`-algebras; the Lean field asks that the
  *natural* map be bijective, which is stronger, is what BGR proves for `Tₙ` (5.2.3/3 (ii):
  *"The map `ī` is the `k`-algebra isomorphism mentioned in (ii)"*, `bgr-5.2.md:152`), and is what
  5.2.5/4 uses (primes of `I[X]` stay prime). [1] formal power series `I⟦X⟧` over `I` satisfy the
  Lean axioms with `W` the Weierstrass polynomials, as BGR says ✓. SURVIVED.
- **N10b** `IsRueckert.ringKrullDim_eq` (complete in the skeleton: `le_antisymm` of L10.10, L10.11).
  [6] hypotheses of the two children are the parent's ✓. SURVIVED.

---

## G11 — Rückert's applications to the Tate algebra (`TateAlgebra/Rueckert.lean`), [RM] §0.3.2–§0.3.4

### Source and prose proof

[BGR] 5.2.5–5.2.6 (`bgr-5.2.md:282–283`, `:366–371`, `:388`, `:392–396`): *"According to the results
of (5.2.2), (5.2.3) and (5.2.4), the algebra `Tₙ` is Rückert over `T_{n−1}` if one takes `W` to be
the family of Weierstrass polynomials in `Xₙ`. … As we have already observed, Theorem 5.2.2/1, Lemma
5.2.3/2 and Propositions 5.2.3/3 and 5.2.4/1 guarantee that `Tₙ` is Rückert over `T_{n−1}`.
Furthermore `T₀ = k` is a Noetherian factorial ring. Thus using induction on `n`, we get from
Propositions 5.2.5/2 and 5.2.5/4 **Theorem 1.** The ring `Tₙ` is Noetherian and factorial. …
**Theorem 2.** `Tₙ` is normal. … **Theorem 3.** `Tₙ` is a Jacobson ring. Proof. Proposition 5.1.3/3
tells us that `j(Tₙ) = 0`. … Since `T₀ = k` is a Jacobson ring, the assertion follows by induction
on `n`."*

### Leaves

- **L11.1** `isRueckert_ofPolynomial` — Q: `bgr-5.2.md:366–368` (quoted above: the four ingredients).
  M: literal: `T_{n+1}` is Rückert over `Tₙ` along `ofPolynomial` for the Weierstrass polynomials. D:
  the five fields are [TOWER] `ofPolynomial_injective`, `IsWeierstrassPolynomial.monic`, L7.19–L7.20
  (`of_mul`), L8.2, and for axiom (3): L9.15, L7.22 (`e⁻¹ · σ(f) = ofPolynomial ω`). A: [6] the
  structure was assembled against the skeleton in `scratch/spot3.lean` (item 1) ✓. [2] `n = 0`:
  `T₁` over `K` ✓. [3] completeness of `K` is needed (L8.2, L7.22) — an explicit binder (defect D5).
  SURVIVED.
- **L11.2** `instIsNoetherianRing`, **L11.3** `instUniqueFactorizationMonoid`, **L11.4**
  `instIsJacobsonRing` — Q: [BGR] 5.2.6/1 and 5.2.6/3 (quoted above). M: literal, as instances. D:
  induction on `n`; base case along [SEAM] `isEmptyEquiv : T₀ ≃+* K`
  (`isNoetherianRing_of_ringEquiv`, `MulEquiv.uniqueFactorizationMonoid`,
  `isJacobsonRing_of_surjective`); step L11.1 with L10.5, L10.8 (domains by L1.5), L10.7 with L2.20.
  A: [1] over a non-complete `K` the statements were claimed by the first skeleton (defect D5);
  now `[CompleteSpace K]` is explicit ✓. [2] `n = 0` ✓. [5] base cases and steps compiled in
  `spot3.lean` (items 2, 3, 3''). SURVIVED. The normality (BGR 5.2.6/2) is an `example` by
  `inferInstance` in the skeleton — Mathlib derives `IsIntegrallyClosed` from factoriality.
- **L11.5** `ringKrullDim_eq` — Q: [BGR] `bgr-6.1.2.md:51` *"and `dim T_d = d`"*. M: literal. D:
  induction; base `ringKrullDim_eq_of_ringEquiv`, `ringKrullDim_eq_zero_of_field`; step N10b with
  L7.18 at `s = 1`. A: [2] `n = 0` ✓. [4] BGR's proof of `≤` is replaced (erratum E5). [5] the step
  compiled in `spot3.lean` (item 3'). SURVIVED.

---

## G12 — Bald subrings (`Bald.lean`), [RM] §0.3.1

### Source and prose proof

[Bo] 1.3/2–3 (`bosch-lectures.txt:767–805`): *"Let `R` be a ring with a multiplicative ring norm
`|·|` such that `|a| ≤ 1` for all `a ∈ R`. (i) `R` is called a B-ring if `{a ∈ R ; |a| = 1} ⊂ R*`.
(ii) `R` is called bald if `sup{|a| ; a ∈ R with |a| < 1} < 1`. … **Proposition 3.** Let `K` be a
field with a valuation and `R` its valuation ring. Then the smallest subring `R′ ⊂ R` containing a
given zero sequence `a₀, a₁, … ∈ R` is bald. Proof. The smallest subring `S ⊂ R` equals either
`ℤ/pℤ` for some prime `p`, or `ℤ`. It is bald, since any valuation on the finite field `ℤ/pℤ` is
trivial and since the ideal `{a ∈ ℤ ; |a| < 1} ⊂ ℤ` is principal. If there is an `ε ∈ ℝ` such that
`|aₙ| ≤ ε < 1` for all `n ∈ ℕ`, we see for trivial reasons that `S[a₀, a₁, …]` is bald. Thus, it is
enough to show that, for a bald subring `S ⊂ R` and an element `a ∈ R` of value `|a| = 1`, the ring
`S[a]` is bald. To do this, we may localize `S` by all elements of value `1` and thereby assume that
`S` is a B-ring. … Let `g = ζⁿ + c₁ζⁿ⁻¹ + … + cₙ ∈ S[ζ]` be a polynomial of minimal degree such that
its reduction `g̃` annihilates `ã` or, in equivalent terms, such that `|g(a)| < 1`. Let `ε < 1` be the
supremum of `|g(a)|` and of all values `|c|` with `c ∈ S` and `|c| < 1`. Now consider a polynomial
`f ∈ S[ζ]` with `|f(a)| < 1`; we want to show `|f(a)| ≤ ε`. Using Euklid's division, we get a
decomposition `f = qg + r` with `q, r ∈ S[ζ]` and `deg r < n = deg g`. Since `|g(a)| ≤ ε`, we may
assume `f = r`. If all coefficients of `r` have value `< 1`, this value must be `≤ ε` and we are
done. On the other hand, if one of the coefficients of `r` has value `1`, the reduction `r̃` of `r`
is non-trivial. But then we have `r̃(ã) = 0`, and this contradicts the definition of `g`"*.

Subrings are subrings of the normed field `K`. Bosch's dichotomy "`ã` transcendental or algebraic
over `S̃`" is rephrased without residue fields: either no monic `g ∈ S[ζ]` has `|g(a)| < 1`, or one
of minimal degree exists; the bridge between "a coefficient of norm one" and "a monic polynomial" is
L12.8, which is where the B-ring property is used (the leading unit coefficient is inverted in `S`).

### Leaves

- **L12.1** `IsBald.mono` — Q: `bosch-lectures.txt:771–772` (definition of bald). M: a subring of a
  bald subring is bald (same `ε`). D: unfolding. SURVIVED ([2] `S = ⊥` ✓).
- **L12.2** `le_unitLocalization`, **L12.3** `mem_unitLocalization_iff` — Q:
  `bosch-lectures.txt:784–785` *"we may localize `S` by all elements of value `1`"*. M: the
  localisation inside `K`, and its elements as fractions `s / u`, `‖u‖ = 1`. D:
  `Subring.subset_closure`; `Subring.closure_induction` with `div_add_div`, `div_mul_div_comm`,
  `norm_mul`. A: [2] `S = ⊥` ✓. [3] no ultrametricity (multiplicativity of the norm of a field
  suffices). [5] verified. SURVIVED.
- **L12.4** `IsBald.unitLocalization`, **L12.5** `isBRing_unitLocalization` — Q: as L12.2, and
  `bosch-lectures.txt:806–807` *"we can always localize `R′` by all elements of value `1` and thereby
  assume that `R′` is a B-ring"*. M: the localisation is bald with the same constant, and is a
  B-ring. D: L12.3, `norm_div`. A: [1] is `‖s/u‖ = ‖s‖`? yes, `‖u‖ = 1` ✓. [2] an element `s/u` of
  norm one has inverse `u/s = u · s⁻¹` with `s⁻¹` a generator ✓. SURVIVED.
- **L12.6** `isBald_bot` — Q: `bosch-lectures.txt:777–779` (quoted above). M: the prime subring is
  bald. D: `Subring.mem_bot`, `IsUltrametricDist.norm_intCast_le_one`; `Nat.find` for the least
  positive `g` with `‖(g : K)‖ < 1`, division with remainder, `Int.natAbs_eq`. A: [1] characteristic
  `p`: `g ≤ p`, `ε = ‖(g : K)‖`, possibly `0` ✓. [2] no positive integer of norm `< 1`: `ε = 0`
  works because the only element of norm `< 1` is `0` ✓. [3] ultrametricity necessary: in `ℝ` the
  integers are not in the unit ball. [5] ⚠ `Int.cast_natAbs` does not exist; `Int.natAbs_eq` does.
  SURVIVED.
- **L12.7** `IsBald.closure_union_of_norm_le` — Q: `bosch-lectures.txt:779–780` *"If there is an
  `ε ∈ ℝ` such that `|aₙ| ≤ ε < 1` for all `n ∈ ℕ`, we see for trivial reasons that
  `S[a₀, a₁, …]` is bald."* M: literal, for any set `T` of elements of norm `≤ ε`. D:
  `Subring.closure_induction` with the invariant "every element is `s + z`, `s ∈ S`,
  `‖z‖ ≤ max ε 0`"; `IsUltrametricDist.norm_add_le_max`,
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`. A: [1] the "trivial reasons" need the
  invariant: an element of norm `< 1` is `s + z` with `‖s‖ < 1`, hence `≤ ε_S` ✓. [2] `T = ∅` ✓;
  `ε < 0`: `T = ∅` ✓. [3] `ε < 1` necessary. SURVIVED.
- **L12.8** `IsBRing.exists_monic_norm_aeval_lt_one` — Q: `bosch-lectures.txt:801–803` *"if one of
  the coefficients of `r` has value `1`, the reduction `r̃` of `r` is non-trivial. But then we have
  `r̃(ã) = 0`"* (a nonzero polynomial over the field `S̃` annihilating `ã` can be made monic). M:
  from `p` with a coefficient of norm one and `‖p(a)‖ < 1`, a *monic* `g` of no larger degree with
  `‖g(a)‖ < 1`. D: let `d` be the largest index with `‖p_d‖ = 1`; the higher terms contribute norm
  `< 1`; divide the truncation by the unit `p_d` (B-ring). `Polynomial.aeval_eq_sum_range`,
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`. A: [1] the proof inverts the coefficient `p_d` of
  norm one inside `S`, which is exactly the B-ring property; whether the statement survives without
  it was not pursued, since its only consumer (L12.9) has a B-ring ✓. [2] `p` constant of norm one: `‖p(a)‖ = 1`, hypothesis `hp` fails ✓. [3]
  `‖a‖ = 1` used for `‖a^i‖ = 1`. SURVIVED.
- **L12.9** `IsBRing.isBald_closure_insert` — Q: `bosch-lectures.txt:781–805` (quoted above). M:
  literal: `S[a]` is bald for a bald B-ring `S` and `‖a‖ = 1`. D: every element of the closure is
  `aeval a p` (`Subring.closure_induction`); the dichotomy; `Nat.find` for the minimal degree;
  `Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`; L12.8. A: [1] first case
  (no monic `g`): then by L12.8 every `p` with `‖p(a)‖ < 1` has all coefficients of norm `< 1`,
  hence `≤ ε_S` ✓ (Bosch's transcendental case). [2] `a ∈ S` ✓ (`g = ζ − a`, `g(a) = 0`). [4] exact,
  with the dichotomy rephrased. SURVIVED.
- **L12.10** `IsBald.closure_insert` — Q: `bosch-lectures.txt:780–785` *"it is enough to show that,
  for a bald subring `S ⊂ R` and an element `a ∈ R` of value `|a| = 1`, the ring `S[a]` is bald. To
  do this, we may localize `S`"*. M: for `‖a‖ ≤ 1`. D: `‖a‖ < 1`: L12.7; `‖a‖ = 1`: L12.4, L12.5,
  L12.9, L12.1 with `Subring.closure_mono`, L12.2. SURVIVED.
- **L12.11** `isBald_closure_range` — Q: [Bo] 1.3/3 `bosch-lectures.txt:774–776`. M: literal, for a
  family null along the cofinite filter. D: the finite set `{i | 1/2 < ‖a i‖}`;
  `Set.Finite.induction_on` with L12.10 from L12.6 (`Subring.closure_empty`, `Subring.closure_eq`,
  `Subring.closure_union`); L12.7 with `ε = 1/2` for the rest; L12.1. A: [1] nullity necessary:
  in a densely valued field the closure of a sequence with `‖aₙ‖ → 1⁻` is not bald ✓. [2] empty
  family ✓. [3] `‖a i‖ ≤ 1` necessary. SURVIVED.

### Internal node

- **N12** the structures `IsBRing`, `IsBald` and `unitLocalization` (complete in the skeleton) —
  source [Bo] 1.3/2. [6] Bosch's definitions are for normed rings; here they are predicates on
  subrings of a normed field, the only case used (Bosch: *"the smallest subring `R′ ⊂ R`"*). [1]
  `IsBald` as stated allows any `ε < 1` including negative ones only if no element of norm `< 1`
  exists — impossible since `0` has norm `0`, so `0 ≤ ε` always ✓. SURVIVED.

---

## G13 — Orthonormal families and bases (`PadicFunctionalAnalysis/Orthonormal.lean`), PFA roadmap §2.2.1–§2.2.2

### Source and prose proof

[Bo] 1.3/5 (`bosch-lectures.txt:820–833`): *"Let `V` be a complete normed `K`-vector space. A system
`(x_ν)_{ν∈N}` of elements in `V`, where `N` is finite or at most countable, is called a (topological)
orthonormal basis of `V` if the following hold: (i) `|x_ν| = 1` for all `ν ∈ N`. (ii) Each `x ∈ V`
can be written as a convergent series `x = Σ_{ν∈N} c_ν x_ν` with coefficients `c_ν ∈ K`. (iii) For
each equation `x = Σ_{ν∈N} c_ν x_ν` as in (ii) we have `|x| = max_{ν∈N} |c_ν|`. In particular, the
coefficients `c_ν` in (ii) are unique. For example, the monomials `ζ^ν ∈ Tₙ` form an orthonormal
basis"*. The `p`-adic functional analysis roadmap's convention 5 and §2.2.2 define the two predicates
by finite sums and a dense span (so that they make sense without completeness) and ask for the
equivalence with Bosch's form; `Orthonormal.lean` reproduces the two definitions verbatim from that
roadmap's `Suggested.lean` and proves the half of the equivalence that this layer consumes.

Finite sums: the defining identity gives `‖a i‖ ≤ ‖Σ a_j e_j‖ ≤ max ‖a_j‖`, hence linear
independence. Convergent sums: the partial sums converge in norm, so both inequalities pass to the
limit; the terms tend to zero, so the coefficients do; uniqueness is the first inequality for the
difference. Existence of expansions is the only statement that needs completeness, and it needs it
of the *field* as well as of the space (defect D7): approximate `x` by finite combinations `x_k`;
their coefficient families are uniformly Cauchy by the first inequality, converge in `K`, and the
limit family is null and sums to `x`.

### Leaves

- **L13.1** `norm_coeff_le_norm_sum`, **L13.2** `norm_sum_le` — Q: `bosch-lectures.txt:829–830`
  *"(iii) … we have `|x| = max_{ν∈N} |c_ν|`"*, for finite sums. M: the two inequalities. D: the
  defining identity in `ℝ≥0`, `nnnorm_smul`, `Finset.le_sup`, `Finset.sup_le`. A: [2] `s = ∅` ✓
  (`hC : 0 ≤ C` is what makes L13.2 true there). [3] no ultrametricity or completeness of `V`. [5]
  verified. SURVIVED.
- **L13.3** `linearIndependent` — Q: `bosch-lectures.txt:831` *"In particular, the coefficients `c_ν`
  in (ii) are unique."* M: for finite combinations. D: `linearIndependent_iff'`, L13.1,
  `norm_le_zero_iff`. SURVIVED.
- **L13.4** `tendsto_cofinite_of_hasSum` — Q: `bosch-lectures.txt:824–825` *"a convergent series
  `x = Σ c_ν x_ν`"*. M: the coefficients of a convergent expansion are null. D:
  `Summable.tendsto_cofinite_zero`, `tendsto_zero_iff_norm_tendsto_zero`, `norm_smul`, `‖e i‖ = 1`.
  SURVIVED ([3] no completeness).
- **L13.5** `norm_coeff_le_of_hasSum`, **L13.6** `norm_le_of_hasSum` — Q: (iii) as L13.1. M: the two
  inequalities for convergent sums. D: `HasSum` as a limit of finite sums, `Filter.Tendsto.norm`,
  `le_of_tendsto` with `Filter.eventually_ge_atTop {i}` and L13.1; `le_of_tendsto'` with L13.2. A:
  [2] `I` empty: `x = 0`, `‖0‖ ≤ C` needs `0 ≤ C` ✓ (hypothesis `hC`). [3] none. SURVIVED.
- **L13.7** `eq_of_hasSum` — Q: `bosch-lectures.txt:831`. M: literal. D: `HasSum.sub`, `sub_smul`,
  L13.5 with `x = 0`. SURVIVED.
- **L13.8** `summable_smul` — Q: `bosch-lectures.txt:824–825`. M: a null coefficient family is
  summable in a complete nonarchimedean space. D:
  `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`. SURVIVED ([3] completeness and
  ultrametricity of `V` necessary; `K` need not be complete).
- **L13.9** `IsOrthonormalBasis.exists_hasSum` — Q: `bosch-lectures.txt:824–826` *"(ii) Each `x ∈ V`
  can be written as a convergent series"* — a clause of Bosch's *definition*, which the roadmap's
  definition (dense span) must imply. M: existence of expansions from density, for `K` and `V`
  complete. D: `mem_closure_iff_seq_limit`, `Finsupp.mem_span_range_iff_exists_finsupp`, L13.1 for
  the uniform Cauchy estimate, completeness of `K`, L13.8, L13.6. A: [1] **counterexample without
  `[CompleteSpace K]`**: `K = ℚ` with the `p`-adic norm, `V = ℚ_[p]`, `e = {1}` (defect D7) — fixed.
  [2] `I` empty: `V = 0` ✓. [3] Bosch assumes `K` complete throughout §1.3
  (`bosch-lectures.txt:813–814`: *"let `K` be a field with a complete non-Archimedean valuation"*),
  so the repaired statement is the source's. [5] a real proof, not a one-liner: a ticket of its own
  with L13.8. SURVIVED after repair.

---

## G14 — Lifting orthonormal bases (`OrthonormalLift.lean`), [RM] §0.3.1

### Source and prose proof

[Bo] 1.3/6 (`bosch-lectures.txt:839–883`): *"Let `K` be a field with a complete valuation and `V` a
complete normed `K`-vector space with an orthonormal basis `(x_ν)_{ν∈N}`. Write `R` for the valuation
ring of `K`, and consider a system of elements `y_μ = Σ_{ν∈N} c_{μν} x_ν ∈ V°`, `μ ∈ M`, where the
smallest subring of `R` containing all coefficients `c_{μν}` is bald. Then, if the residue classes
`ỹ_μ ∈ Ṽ` form a `k`-basis of `Ṽ`, the elements `y_μ` form an orthonormal basis of `V`. Proof. … In
particular, `(y_μ)_{μ∈M}` is an orthonormal basis of a subspace `V′ ⊂ V`. Now let `S` be the smallest
complete B-ring in `R` containing all coefficients `c_{μν}`. Then `S` is bald by our assumption; let
`ε = sup{|a| ; a ∈ S, |a| < 1}`. … Then `S̃` is a subfield of the residue field `k` of `R`, and we
have `Ṽ′ = V′_{S̃} ⊗_{S̃} k`, `Ṽ = V_{S̃} ⊗_{S̃} k`. From `Ṽ′ = Ṽ` and `V′_{S̃} ⊂ V_{S̃}` we get
`V′_{S̃} = V_{S̃}`. The latter implies that, for any `x_ν`, there is an element `z_ν ∈ V′_S` satisfying
`|x_ν − z_ν| ≤ ε`. Then, more generally, for any `x ∈ V_S`, there is an element `z ∈ V′_S` with
`|z| = |x|` and `|x − z| ≤ ε|x|`. But then, as `V′_S` and `V_S` are complete, we get `V′_S = V_S` by
iteration."*

The reduction of `V` is represented by coordinates: the reduction of `y_μ` is the finitely supported
family `r μ` of the residues of its coordinates `c μ ν` (a hypothesis `hr` ties them), so no quotient
module is built. The three steps of Bosch's proof are three leaves. (a) Independence of the `r μ`
gives orthonormality of `y`: scale a finite combination so that its largest coefficient is `1`; the
reduction of the combination is a nontrivial combination of the `r μ`, hence nonzero, so some
coordinate has norm one. (b) Spanning gives approximation: the basis vector `δ_ν` is a `k`-combination
of the `r μ`; all the vectors involved have coordinates in the subfield `S̃` (after localising `S` to
a B-ring, G12), and a linear system over a subfield that is solvable over the field is solvable over
the subfield ("`V′_{S̃} ⊗ k = V_{S̃} ⊗ k` and `V′_{S̃} ⊂ V_{S̃}` give `V′_{S̃} = V_{S̃}`"); lifting the
solution to `S` gives `z_ν` with all coordinates of `x_ν − z_ν` in `S`, of norm `< 1`, hence `≤ ε`.
(c) Approximation up to a uniform `ε < 1` gives density, by BGR 1.1.4/2 ([SEAM]
`AddSubgroup.dense_of_infDist_le`), which replaces "by iteration" and needs no completeness. The
conclusion `IsOrthonormalBasis` (orthonormal with dense span) therefore holds without completeness
of `K` or `V`; Bosch's expansion form then follows from L13.9 where both are complete.

### Leaves

- **L14.1** `Finsupp.mem_span_range_of_mapRange_mem_span` — Q: `bosch-lectures.txt:869–874` *"Then
  `S̃` is a subfield of the residue field `k` of `R`, and we have `Ṽ′ = V′_{S̃} ⊗_{S̃} k`,
  `Ṽ = V_{S̃} ⊗_{S̃} k`. From `Ṽ′ = Ṽ` and `V′_{S̃} ⊂ V_{S̃}` we get `V′_{S̃} = V_{S̃}`."* M: descent of
  solvability from a field `E` to a subfield `F`, in coordinates. D:
  `LinearMap.exists_leftInverse_of_injective` for `Algebra.linearMap F E` gives an `F`-linear
  retraction `π`; apply it coefficientwise (`Finsupp.mem_span_range_iff_exists_finsupp`,
  `Finsupp.mapRange`, `Finsupp.sum_apply`). A: [1] for rings instead of fields the statement fails
  (`F = ℤ`, `E = ℚ`, `v = 2`, `w = 1`) — fields are necessary ✓. [2] `M` empty: `w = 0` ✓. [3] `F`,
  `E` in different universes ✓. [5] verified. SURVIVED.
- **L14.2** `Subring.IsBRing.residueSubfield` (six `sorry` fields) — Q: `bosch-lectures.txt:785–786`
  *"Then `S` contains a unique maximal ideal `𝔪`, and `S̃ = S/𝔪` is a field."* M: the image of `S` in
  the residue field of `K` is a subfield. D: closure under ring operations from `S` being a subring
  and `residue` a ring homomorphism; inverses from `IsBRing.inv_mem` when `‖s‖ = 1`
  (`eq_inv_of_mul_eq_one_right`) and `inv_zero` when `‖s‖ < 1`. A: [2] `S = ⊥` ✓. [3] the B-ring
  property is used exactly for `inv_mem'`. [5] verified. SURVIVED.
- **L14.3** `IsOrthonormalFamily.of_linearIndependent_residue` — Q: `bosch-lectures.txt:849–851`
  *"The systems `(x̃_ν)` and `(ỹ_μ)` form a `k`-basis of `Ṽ`. … In particular, `(y_μ)_{μ∈M}` is an
  orthonormal basis of a subspace `V′ ⊂ V`."* M: independence of the reductions implies
  orthonormality of the family. D: L13.5, L13.6 for `‖y μ‖ = 1` (`LinearIndependent.ne_zero`);
  for a finite combination: `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, scaling by the
  largest coefficient, `hasSum_sum`, `HasSum.const_smul`, `linearIndependent_iff'`, L13.5. A: [1]
  without independence: `y₁ = x₁`, `y₂ = x₁ + p x₂` have `‖y₁ − y₂‖ = |p| < max` ✓ necessary. [2]
  `M` empty ✓; `s = ∅` ✓. [3] no baldness, no completeness. SURVIVED.
- **L14.4** `exists_norm_sub_le_of_span_residue` — Q: `bosch-lectures.txt:874–876` *"The latter
  implies that, for any `x_ν`, there is an element `z_ν ∈ V′_S` satisfying `|x_ν − z_ν| ≤ ε`."* M:
  literal, with `ε` the bald constant of the localisation of `S`. D: L12.4, L12.5, L14.2, L14.1,
  `Finsupp.onFinset` to view the `r μ` over the subfield, `hasSum_sum`, `hasSum_ite_eq` for the
  expansion of `x ν`, L13.6. A: [1] **baldness is necessary**: in `c₀(ℕ, ℂ_p)`,
  `y n = x n − π n • x (n+1)` with `∏ |π n| > 0` reduces to the standard basis and its closed span
  misses `x 0` (module docstring) ✓. [2] `N` empty ✓. [3] no completeness. [5] the longest discharge
  of the file — a ticket of its own. SURVIVED.
- **L14.5** `dense_span_of_forall_exists_norm_sub_le` — Q: `bosch-lectures.txt:879–883` *"Then, more
  generally, for any `x ∈ V_S`, there is an element `z ∈ V′_S` with `|z| = |x|` and `|x − z| ≤ ε|x|`.
  But then, as `V′_S` and `V_S` are complete, we get `V′_S = V_S` by iteration."* M: uniform
  approximation of the basis vectors implies density of the span. D: [SEAM]
  `AddSubgroup.dense_of_infDist_le` (BGR 1.1.4/2) with `ε′ = max ε (1/2)`; density of
  `span (range x)`; L13.1; `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`. A: [2] `ε ≤ 0`:
  handled by `ε′` ✓; `V = 0` ✓. [3] no completeness — "iteration" is replaced by the density lemma,
  whose hypotheses are `0 < ε′ < 1`. [4] the leaf states density over `K`, not Bosch's equality of
  `S`-modules; that is all the conclusion needs. SURVIVED.
- **L14.6** `IsOrthonormalBasis.of_residue_basis` — Q: [Bo] 1.3/6 (statement, quoted above). M:
  literal, with the conclusion in the dense-span form. D: assembly `⟨L14.3, L14.5 ∘ L14.4⟩`. A: [6]
  hypotheses of L14.3 (`‖c μ ν‖ ≤ 1`) come from `S.IsBald.norm_le_one` ✓. [3] `[CompleteSpace V]`
  removed (defect D4). [4] Bosch requires `N` countable; nothing here uses it. SURVIVED.

---

## G15 — Ideals are strictly closed (`TateAlgebra/StrictlyClosed.lean`), [RM] §0.3.1, §0.3.5

### Source and prose proof

[Bo] 1.3/7–10 (`bosch-lectures.txt:885–993`). Corollary 7: *"Let `a` be an ideal in `Tₙ`. Then there
are generators `a₁, …, a_r` of `a` satisfying the following conditions: (i) `|aᵢ| = 1` for all `i`.
(ii) For each `f ∈ a`, there are elements `f₁, …, f_r ∈ Tₙ` such that `f = Σ fᵢaᵢ`, `|fᵢ| ≤ |f|`.
Proof. Let `ã` be the reduction of `a`; i.e., the image of `a ∩ R⟨ζ⟩` under the reduction map … Then
`ã` is an ideal in the noetherian ring `k[ζ]` and, hence, finitely generated, say by the residue
classes `ã₁, …, ã_r` of some elements `a₁, …, a_r ∈ a` having norm equal to `1`. As the elements
`ζ^ν ãᵢ` … generate `ã` as a `k`-vector space, we can find a system `(y_μ)_{μ∈M′}` of elements of
type `ζ^ν aᵢ ∈ a` such that its residue classes form a `k`-basis of `ã`. Adding monomials of type
`ζ^ν`, `ν ∈ ℕⁿ`, we can enlarge the system to a system `(y_μ)_{μ∈M}` such that its residue classes
form a `k`-basis of `k[ζ]`. … Now apply Proposition 3 and Theorem 6. … Choose `f ∈ a`. Then, since
`(y_μ)_{μ∈M}` is an orthonormal basis of `Tₙ`, there is an equation `f = Σ_{μ∈M} c_μ y_μ` with
certain coefficients `c_μ ∈ K` satisfying `|c_μ| ≤ |f|`. Writing `f′ = Σ_{μ∈M′} c_μ y_μ`, the choice
of the elements `y_μ`, `μ ∈ M′`, implies that we can write `f′ = Σ fᵢaᵢ` with certain elements
`fᵢ ∈ Tₙ` satisfying `|fᵢ| ≤ |f|`. In particular, `f′ ∈ a`, and we are done if we can show `f = f′`.
… Assuming `|f| = 1`, we would get a non-trivial equation `f̃ = Σ_{μ∈M−M′} c̃_μ ỹ_μ` for the element
`f̃ ∈ ã` which, however, contradicts the construction of the elements `ỹ_μ`."* Corollary 8: *"Each
ideal `a ⊂ Tₙ` is complete and, hence, closed in `Tₙ`."* Corollary 9: *"Each ideal `a ⊂ Tₙ` is
strictly closed; i.e., for each `f ∈ Tₙ` there is an element `a₀ ∈ a` such that
`|f − a₀| = inf_{a∈a} |f − a|`. Proof. … the assertion of the corollary holds for
`a₀ = Σ_{μ∈M′} c_μ y_μ`."* Corollary 10 is the same for submodules `N ⊂ Tₙˢ` with the maximum norm.
[BGR] 5.2.7/8 (`bgr-5.2.md:492–493`): *"Each ideal `𝔞 ⊂ Tₙ` is strictly closed in `Tₙ`, and the
residue norm on `Tₙ/𝔞` satisfies `|Tₙ/𝔞| = |Tₙ| = |k|`."*

The board proves Corollary 10 (submodules of `T^ι`, `ι` finite) and specialises to ideals at
`ι = Unit`. BGR's own proof of 5.2.7/7 is an induction on `n` through cartesian modules over
`Q(Tₙ)` (Lemmas 9, 10, results of Chapter 2) and through 5.2.7/1, which cites 3.7.3 — none of it is
in the chain; Bosch's route needs only G12–G14 and the reduction (erratum E6: [RM] §0.3.1 and §0.3.5
say closedness is "cited" from the adic and functional-analysis roadmaps, which this chain does not
contain).

The steps, in Bosch's order: (1) the monomial vectors `X^ν eᵢ` are an orthonormal basis of `T^ι`;
(2) the reduction `Ñ` of `N` is a `k[X]`-submodule of `k[X]^ι`, finitely generated because `k[X]` is
noetherian (finitely many variables), by reductions of elements `g_j ∈ N` of norm one; (3) linear
algebra over `k`: some multiples `X^ν g̃_j` form a `k`-basis of `Ñ`, and some monomial vectors
complete them to a `k`-basis of `k[X]^ι` — the "adapted family"; (4) the coordinates of the lifted
adapted family are coefficients of the finitely many `g_j`, a null family, so they lie in a bald
subring (L12.11), and the lifting theorem (L14.6) makes the adapted family an orthonormal basis of
`T^ι`; (5) a convergent combination of the multiples `X^ν g_j` regroups as `Σ q_j g_j` with
`‖q_j‖ ≤ sup |c_μ|`; (6) the expansion of an element of `N` has no monomial-vector part (Bosch's
contradiction with the construction of the `ỹ_μ`); (7) for any `f`, the part of its expansion along
the multiples is a nearest point of `N`, and the corollaries follow.

### Leaves

- **L15.1** `MvPolynomial.exists_basis_adaptedFamily` — Q: `bosch-lectures.txt:973–978` *"there
  exists a system `(y_μ)_{μ∈M′}` of elements of type `ζ^ν xᵢ ∈ N` such that their residue classes
  form a `k`-basis of `Ñ`. … Then it is possible to enlarge the system … by adding elements of type
  `ζ^ν e_j` in such a way that the residue classes of the `y_μ`, `μ ∈ M`, form a `k`-basis of
  `k[ζ]ˢ`."* M: literal, as a statement about `k[X]^ι`: index sets `A`, `B` with the adapted family
  linearly independent, spanning, and its `A`-part spanning the `k[X]`-submodule generated by the
  `h j`. D: `LinearIndepOn.extend` (twice: from `∅` inside the multiples, then inside multiples ∪
  monomial vectors), `LinearIndepOn.linearIndepOn_extend`, `subset_extend`, `subset_span_extend`;
  `Pi.basis` of `MvPolynomial.basisMonomials` for "the monomial vectors span"; `MvPolynomial.as_sum`
  and `MvPolynomial.monomial_mul` for "the multiples span the submodule". A: [1] repeated vectors
  (`h 1 = h 2`, or `h j = 0`) are why the choice is of *index sets* via `LinearIndepOn` rather than
  of a set of vectors ✓. [2] `r = 0`: `A = ∅`, `B` everything ✓; `ι` empty ✓. [3] `σ` need not be
  finite here. [5] verified names; `spot3.lean` (item 6) checks the basis. SURVIVED.
- **L15.2** `isOrthonormalBasis_monomial`, **L15.3** `isOrthonormalBasis_single_monomial` — Q:
  `bosch-lectures.txt:832–833` *"the monomials `ζ^ν ∈ Tₙ` form an orthonormal basis"* and `:981–983`
  *"the canonical system `Z = (ζ^ν e_j)`, which is an orthonormal basis of `Tₙˢ`"*. M: literal, in
  the dense-span form. D: [SEAM] `norm_monomial`; L1.9, L1.11 for the finite-sum identity; L1.7 for
  density; for the product, `Pi.norm_single`, `Pi.norm_def`, and density of a finite product. A:
  [2] `ι` empty ✓; `σ` empty: one vector ✓. [3] no completeness. [5] verified. SURVIVED.
- **L15.4** `hasSum_coeff_smul_single_monomial` — Q: `bosch-lectures.txt:984–985` *"to represent the
  elements `xᵢ` … in terms of the orthonormal basis `Z`, using converging linear combinations with
  coefficients in `K`"*. M: the expansion of a tuple in the monomial vectors has the coefficients of
  its components as coordinates. D: `Pi.hasSum`, `Function.Injective.hasSum_iff` along
  `t ↦ ⟨i, t⟩`, [SEAM] `hasSum_monomial`. SURVIVED ([2] `f = 0` ✓).
- **L15.5** `reductionPi_eq_zero_iff` — Q: [Bo] `bosch-lectures.txt:390–391`, componentwise. D:
  L2.6, `pi_norm_lt_iff`. SURVIVED ([2] `ι` empty: both sides true ✓).
- **L15.6** `reductionSubmodule` (three `sorry` fields) — Q: `bosch-lectures.txt:969–971` *"Writing
  `Ñ` for the image of `N ∩ (R⟨ζ⟩)ˢ`, we see that `Ñ` is a `k[ζ]`-submodule of `(k[ζ])ˢ`"*. M:
  literal. D: `add_mem'` by the ultrametric inequality on `ι → T` and additivity of the reduction;
  `smul_mem'` by lifting a polynomial through L2.12 and multiplicativity. A: [1] is the carrier
  closed under scalars not in the image of `T⁰`? every polynomial is a reduction (L2.12) ✓. [2]
  `N = ⊥`: `Ñ = ⊥` ✓. SURVIVED.
- **L15.7** `exists_generators_reductionSubmodule` — Q: `bosch-lectures.txt:971–973` *"hence,
  finitely generated, since `k[ζ]` is noetherian. Thus, we can choose elements `x₁, …, x_r ∈ N` of
  norm `1` such that their residue classes `x̃₁, …, x̃_r` generate `Ñ` as `k[ζ]`-module."* M: literal.
  D: `MvPolynomial.isNoetherianRing`, `isNoetherian_pi`, `IsNoetherian.noetherian`,
  `Submodule.fg_def`; drop the zero generators and use L15.5 for norm one; `Finset.equivFin`. A: [1]
  `σ` infinite: `k[X]` is not noetherian and `Ñ` need not be finitely generated — `[Finite σ]`
  necessary ✓. [2] `Ñ = ⊥`: `r = 0` ✓. SURVIVED.
- **L15.8** `exists_isBald_forall_coeff_mem` — Q: `bosch-lectures.txt:985–987` *"we need finitely many
  zero sequences in `R`, and the smallest subring `R′ ⊂ R` containing all these coefficients is bald
  by Proposition 3."* M: literal. D: L12.11 for the family indexed by `Fin r × ι × (σ →₀ ℕ)`; L1.13,
  L1.9. SURVIVED ([2] `r = 0`: the closure of the empty family is `⊥`, bald by L12.6 ✓; [3]
  finiteness of `ι` used).
- **L15.9** `isOrthonormalBasis_adaptedFamily` — Q: `bosch-lectures.txt:987–991` *"Since the elements
  `y_μ`, `μ ∈ M′`, are obtained from `x₁, …, x_r` by multiplication with certain monomials `ζ^ν` …,
  we see that `y_μ ∈ Σ̂_{z∈Z} R′z` for all `μ ∈ M`. Thus, by Theorem 6, `(y_μ)_{μ∈M}` is an
  orthonormal basis of `Tₙˢ`"*. M: literal. D: L14.6 with `x` := L15.3, coordinates from L15.4, the
  bald subring of L15.8, and `r μ` := the coordinates of the reduced adapted family in
  `Pi.basis … basisMonomials`. A: [6] the coordinates of `X^ν g_j` are coefficients of `g_j` or `0`,
  those of a monomial vector are `0` or `1`, all in the bald subring ✓; reduction commutes with the
  adapted family (`reduction` multiplicative, reduction of a monomial) ✓. [3] no completeness. [5]
  the bridge between two index conventions — a ticket shared only with L15.8. SURVIVED.
- **L15.10** `exists_eq_sum_smul_of_hasSum` — Q: `bosch-lectures.txt:911–914` *"Writing
  `f′ = Σ_{μ∈M′} c_μ y_μ`, the choice of the elements `y_μ`, `μ ∈ M′`, implies that we can write
  `f′ = Σ fᵢaᵢ` with certain elements `fᵢ ∈ Tₙ` satisfying `|fᵢ| ≤ |f|`."* M: literal, with the bound
  `C` in place of `|f|`. D: `q j := Σ'` of the monomials `c_μ X^ν` over the indices with second
  component `j` (summable: null family in the complete `T`);
  `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`; `HasSum.smul_const`, `hasSum_sum`,
  `HasSum.unique`. A: [1] `C < 0` (defect D2) — `hC0` ✓. [2] `A` empty: `q = 0` ✓. [3] `hc0`
  (nullity of `c`) is needed to define `q j` and is available to the consumer from L13.4. SURVIVED.
- **L15.11** `coeff_inr_eq_zero_of_mem` — Q: `bosch-lectures.txt:915–925` *"we may replace `f` by
  `f − f′ = Σ_{μ∈M−M′} c_μ y_μ ∈ a` and thereby assume `c_μ = 0` for `μ ∈ M′`. Then, if `f ≠ 0`,
  there is an index `μ ∈ M − M′` with `c_μ ≠ 0`. Assuming `|f| = 1`, we would get a non-trivial
  equation `f̃ = Σ_{μ∈M−M′} c̃_μ ỹ_μ` for the element `f̃ ∈ ã` which, however, contradicts the
  construction of the elements `ỹ_μ`."* M: literal: the expansion of an element of `N` has no
  monomial-vector coefficients. D: L13.4, L15.10 (the `A`-part lies in `N`),
  `Function.Injective.hasSum_iff`, `HasSum.sub`, [PFA] `Filter.Tendsto.exists_forall_norm_le` for the
  largest coefficient, the reduction of a convergent expansion with coefficients in `K⁰` (a private
  lemma: only the finitely many coefficients of norm one survive, [PFA]
  `IsUltrametricDist.norm_tsum_lt_of_forall_lt`), `LinearIndependent.disjoint_span_image`. A: [1]
  `hA` is necessary: without "the `A`-part spans `Ñ`" the reduced element could need monomial
  vectors ✓. [2] `B` empty: vacuous ✓; `x = 0` ✓ (L13.7). [5] the deepest leaf of the board — a
  ticket of its own. SURVIVED.
- **L15.12** `exists_isOrthonormalBasis_adaptedFamily` — Q: `bosch-lectures.txt:930–934` *"the system
  `(y_μ)_{μ∈M′}` is seen to be an orthonormal basis of `a`. Namely, `(y_μ)_{μ∈M′}` is part of an
  orthonormal basis of `Tₙ` and, as we have seen in the proof above, any convergent series
  `Σ_{μ∈M′} c_μ y_μ` … gives rise to an element of `a`."* M: existence of generators and an adapted
  orthonormal basis in which elements of `N` have no monomial-vector part. D: assembly of L15.7,
  L15.1, L15.9, L15.11 — compiled against the skeleton in `scratch/spot4.lean`. SURVIVED.
- **L15.13** `exists_generators_forall_exists_isNearest` — Q: [Bo] 1.3/9 `bosch-lectures.txt:949–954`
  *"we use the orthonormal basis `(y_μ)_{μ∈M}` of `Tₙ` and write `f = Σ_{μ∈M} c_μ y_μ` with
  coefficients `c_μ ∈ K`. As `M′ ⊂ M` is a subset such that `(y_μ)_{μ∈M′}` is an orthonormal basis
  of `a`, the assertion of the corollary holds for `a₀ = Σ_{μ∈M′} c_μ y_μ`."* M: one statement from
  which 1.3/7, 1.3/8, 1.3/9 and BGR 5.2.7/8 all follow: generators `g_j` of norm one such that every
  `f` has `Σ q_j g_j`, `‖q_j‖ ≤ ‖f‖`, a nearest point of `N`. D: L15.12, L13.9 (`K` complete), L13.4,
  L13.5, L15.10, L13.6, L13.7. A: [2] `N = ⊥`: `r = 0`, the nearest point is `0` ✓; `N = ⊤` ✓; `f = 0`
  ✓. [3] `[CompleteSpace K]` and `[Finite σ]` both used. [4] the bundling is a shared-witness
  existential (the generators), not a conjunction of independent facts. SURVIVED.
- **L15.14** `exists_generators_norm_le` — Q: [Bo] 1.3/10 `bosch-lectures.txt:956–967`; [BGR] 5.2.7/1
  with `ρ = 1` (`bgr-5.2.md:420`: *"generating systems admitting the bound `ρ = 1`"*). D: L15.13
  applied to `x ∈ N` (the nearest point is `x` itself) — proved in `spot4.lean`. SURVIVED.
- **L15.15** `exists_forall_norm_sub_le` — Q: [BGR] 5.2.7/7 `bgr-5.2.md:486–487` *"`M` is … strictly
  closed in `F`"*; [Bo] 1.3/9. D: L15.13. SURVIVED.
- **L15.16** `isClosed_submodule` — Q: [Bo] 1.3/8 `bosch-lectures.txt:935` *"Each ideal `a ⊂ Tₙ` is
  complete and, hence, closed in `Tₙ`"*, for submodules. D: L15.15, `Metric.mem_closure_iff`. A: [4]
  Bosch proves closedness from 1.3/7 by summing series; from strict closedness it is immediate.
  SURVIVED.
- **L15.17** `infDist_mem_range_norm` — Q: [BGR] 5.2.7/8 `bgr-5.2.md:492–493` (`|Tₙ/𝔞| = |k|`), for
  submodules of `T^ι` ([RM] §0.3.5: *"a finite `Tₙ`-module is the quotient of a free module by a
  strictly closed submodule, so that its residue norm takes values in `|K|`"*). D: L15.15,
  `Metric.le_infDist`, `Metric.infDist_le_dist_of_mem`, `Pi.norm_def`, `Finset.exists_mem_eq_sup`,
  L1.15. A: [2] `ι` empty: distance `0 = ‖(0 : K)‖` ✓; `N` is nonempty as a set, so `infDist` is not
  the junk value ✓. SURVIVED.
- **L15.18** `exists_generators_norm_le_ideal`, **L15.19** `exists_forall_norm_sub_le_ideal`,
  **L15.20** `isClosed_ideal` — Q: [Bo] 1.3/7, 1.3/9, 1.3/8 (quoted above); [BGR] 5.2.7/2
  `bgr-5.2.md:418` *"All ideals of `Tₙ` are closed."* D: L15.14–L15.16 for `ι = Unit` and the
  submodule `{x | x () ∈ I}`. SURVIVED ([2] `I = ⊥`, `I = ⊤` ✓).
- **L15.21** `norm_quotient_mk_mem_range_norm` — Q: [BGR] 5.2.7/8 (quoted above). M: the quotient
  seminorm of `T ⧸ I` takes values in `‖K‖`. D: `QuotientAddGroup.norm_mk` (the quotient norm is the
  distance to `I`), L15.17 at `ι = Unit` or L15.19 with L1.15. SURVIVED ([5] the norm on `T ⧸ I` is
  Mathlib's quotient seminorm, defined for every ideal; L15.20 makes it a norm).

### Internal nodes

- **N15** the chain L15.12 → L15.13 → corollaries. [6] could L15.12 hold and L15.13 fail? L15.13
  needs expansions of arbitrary `f` (L13.9, hence completeness of `K` and of `T^ι`, both present) and
  that the `A`-part of an expansion lies in `N` with bounded coefficients (L15.10 with the nullity
  from L13.4) ✓. [4] the tree is Bosch's proof of 1.3/7 and 1.3/10, step for step; the only
  re-ordering is that the nearest-point statement (Bosch's 1.3/9, proved "going back to the proof of
  Corollary 7") is proved first and 1.3/7, 1.3/8 are read off it. SURVIVED.

---

## G16 — Weakly stable fields (`WeaklyStable.lean`), [RM] §0.4.1

### Source and prose proof

[BGR] 2.2.5/1, 2.3.1/2–3, 2.3.2/1–2 (`bgr-2.md:11–13`, `:121–133`, `:151–167`): *"A normed `A`-module
`M` is called … b-separable if for each `x ≠ 0` in `M` there exists a bounded `A`-linear map
`λ: M → A` such that `λ(x) ≠ 0`. … **Proposition 2.** If a finite-dimensional normed space `U` is
b-separable, then each `K`-linear map `U → K` is bounded. Proof. It is enough to construct
`n := dim_K U` linearly independent bounded `K`-linear maps `λ₁, …, λₙ` of `U` into `K`, since each
`K`-linear map is a linear combination of these and hence bounded. … **Corollary 3.** A
finite-dimensional normed space `U` is b-separable if and only if `Hom_K(U, K) = ℒ(U, K)`. …
**Definition 2.** A normed `K`-vector space `V` is called weakly cartesian … if the conditions of
Theorem 1 are fulfilled"* (condition (3): each finite-dimensional subspace is b-separable). [BGR]
3.5.1/3–4, 3.5.2/1 (`bgr-3.5.md:57–71`, `:80–90`): *"**Proposition 3.** Let `L` be a finite separable
extension of `K` such that the trace function `T := Tr_{L/K} : L → K` is continuous. Then `L` is
weakly `K`-cartesian. Proof. … Since `L` is a separable extension, `T(xy)` is non-degenerate, i.e.,
for given `x₀ ≠ 0` in `L`, there always exists a `y₀ ∈ L` such that `T(x₀y₀) ≠ 0`. Hence
`x ↦ T(xy₀)` is a continuous `K`-linear map `λ: L → K` such that `λ(x₀) ≠ 0`. Thus `L` is a
b-separable `K`-vector space … **Proposition 4.** If `K` is perfect (in particular, if `K` is of
characteristic 0) the algebraic closure `K_a` of `K` provided with the spectral norm is weakly
`K`-cartesian. Proof. The field `K` being perfect, each finite extension `L ⊂ K_a` is separable. The
trace function `T: L → K` is a contraction with respect to the spectral norm on `L` (see Corollary
3.2.3/2). … **Definition 1.** A valued field `K` is called weakly stable if each finite extension `L`
of `K` provided with the spectral norm is weakly `K`-cartesian. … By Proposition 3.5.1/4, each
perfect field is weakly stable. Furthermore, it follows from Proposition 2.3.3/4 that each complete
field `K` is weakly stable."* [BGR] 3.2.3/2 (`bgr-3.2.md:49–54`): *"The `K`-linear trace map
`Tr_{L/K} : L → K` is a contraction … Proof. We have
`|Tr_{L/K} y| = |a₁| ≤ max_{1≤ν≤n} |a_ν|^{1/ν} = σ(ξ) = |y|_sp`."*

For a finite extension, "weakly cartesian" is "b-separable", i.e. (2.3.1/3) "every `K`-linear
functional is bounded for the spectral norm"; that is the definition `IsWeaklyStable`, stated with
`spectralNorm` as a function so that no normed structure on `L` is needed. ⚠ [RM] §0.4.1 attributes
the route to "BGR 3.5.3" and "3.5.4"; in characteristic zero the route is 3.5.1/3–4 (erratum E7).
The fraction field of a normed domain with multiplicative norm carries the unique multiplicative
extension `|a/b| = ‖a‖/‖b‖` ([BGR] `bgr-3.5.md:143–144`: *"`K` is the field of fractions of `A`, and
the valuation on `K` extends the valuation on `A`"*); it is packaged as an `AbsoluteValue` and a
reducible `NormedField` definition, not an instance, so that `Q(Tₙ)` is a normed field only where a
statement says so.

### Leaves

- **L16.1** `Module.Dual.exists_bound_of_forall_exists_ne_zero` — Q: [BGR] 2.3.1/2 (quoted above).
  M: literal, with an arbitrary function `N : V → ℝ` in place of the norm. D: the functionals bounded
  with respect to `N` form a subspace `W` of the dual; the hypothesis says
  `W.dualCoannihilator = ⊥`; `Subspace.dualAnnihilator_dualCoannihilator_eq` gives `W = ⊤`. A: [1]
  is any property of `N` needed (nonnegativity, homogeneity)? No: closure of `W` under addition and
  scalars uses only `(C₁ + C₂) * N y = C₁ * N y + C₂ * N y` and `‖a‖ ≥ 0` ✓ — an unconstrained
  parameter that is genuinely unconstrained. [2] `V = 0` ✓. [3] finite dimension necessary. [4] BGR
  builds a basis of bounded functionals by induction; the double-annihilator lemma is the same
  statement. SURVIVED.
- **L16.2** `norm_trace_le_spectralNorm` — Q: [BGR] 3.2.3/2 (quoted above). M: literal. D:
  `trace_eq_finrank_mul_minpoly_nextCoeff`, `IsUltrametricDist.norm_natCast_le_one`,
  `Polynomial.nextCoeff`, `minpoly.natDegree_pos`, `spectralValueTerms_of_lt_natDegree`,
  `spectralValueTerms_bddAbove`, `le_ciSup`. A: [1] archimedean `K`: `Tr_{ℂ/ℝ}(1) = 2 > 1` —
  ultrametricity necessary and present ✓. [2] `x ∈ K`: trace `[L:K] · x`, norm `≤ ‖x‖` ✓. [3] no
  completeness. [4] BGR uses the field polynomial `ξ = q^m`; Mathlib's trace formula uses the
  minimal polynomial `q` and the degree `m`, the same computation. SURVIVED.
- **L16.3** `exists_bound_of_isSeparable` — Q: [BGR] 3.5.1/3 (quoted above). M: literal for the
  spectral norm, where the trace is a contraction. D: L16.1 with `N := spectralNorm K L`;
  `traceForm_nondegenerate`; L16.2; `spectralAlgNorm` and `map_mul_le_mul` for
  `|x y₀|_sp ≤ |x|_sp |y₀|_sp`. A: [1] inseparable `L`: the trace is `0` and the argument gives
  nothing — separability necessary for this proof (and BGR's example `bgr-3.5.md:75–78` shows the
  conclusion can fail) ✓. [3] no completeness, no nontriviality of the valuation. SURVIVED.
- **L16.4** `isWeaklyStable_of_perfectField` — Q: [BGR] `bgr-3.5.md:89` *"By Proposition 3.5.1/4,
  each perfect field is weakly stable."* D: `Algebra.IsAlgebraic.isSeparable_of_perfectField`, L16.3.
  SURVIVED.
- **L16.5** `isWeaklyStable_of_completeSpace` — Q: [BGR] `bgr-3.5.md:89–90` *"Furthermore, it follows
  from Proposition 2.3.3/4 that each complete field `K` is weakly stable."* D: the spectral
  normed-field structure on `L` (`spectralNorm.normedField`, `.normedAlgebra`),
  `LinearMap.toContinuousLinearMap` (finite-dimensional over a complete field),
  `ContinuousLinearMap.le_opNorm`. A: [3] Mathlib's finite-dimensional continuity needs
  `NontriviallyNormedField` — present; for a trivially valued complete field the statement is also
  true but is not claimed. [4] BGR's 2.3.3/4 is Mathlib's continuity of linear maps on
  finite-dimensional spaces over a complete field. SURVIVED.
- **L16.6** `IsFractionRing.normAbsoluteValue` (four `sorry` fields), **L16.7**
  `normAbsoluteValue_algebraMap`, **L16.8** `normAbsoluteValue_div` — Q: [BGR] `bgr-3.5.md:143–144`
  (quoted above). M: the extension `|a/b| = ‖a‖/‖b‖` is a well-defined absolute value extending the
  norm. D: `IsLocalization.sec_spec`, `IsFractionRing.injective`, `norm_mul`,
  `IsFractionRing.div_surjective`; the independence of the representative is proved first for the
  raw function and gives L16.8, from which the four fields and L16.7 follow. A: [1] without
  `NormMulClass` the function is not well defined (defect D6) ✓ fixed. [2] `A` a field: `Q = A` ✓.
  [3] `Nontrivial A` is needed for `nonZeroDivisors` to exclude `0`. SURVIVED.
- **L16.9** `isNonarchimedean_normAbsoluteValue`, **L16.10** `IsFractionRing.isUltrametricDist` — Q:
  as L16.6 (*"the valuation on `K`"* is nonarchimedean). D: L16.8 on a common denominator,
  `IsUltrametricDist.norm_add_le_max`;
  `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`. SURVIVED.

### Internal node

- **N16** the definition `IsWeaklyStable` — source [BGR] 3.5.2/1 with 2.3.2/1 (3) and 2.3.1/3. [6] is
  "every functional on `L` is bounded" equivalent to BGR's "weakly cartesian" for a finite extension?
  A finite-dimensional `L` is weakly cartesian iff each of its subspaces is b-separable; subspaces of
  b-separable spaces are b-separable (`bgr-2.md:15`), so iff `L` is b-separable, iff every functional
  is bounded (2.3.1/3) ✓. [2] `L = K`: every functional is a multiple of the identity ✓. [4] [RM]
  §0.4.1 phrases it with maps into arbitrary normed spaces; for finite-dimensional `L` the two are
  equivalent (coordinates), and BGR's form is the one its proofs use. Universe: `L : Type u` in the
  universe of `K`, as for `IsJapaneseRing`. SURVIVED.

---

## G17 — Japanese rings (`Japanese.lean`), [RM] §0.4.3

- **L17.1** `isJapaneseRing_of_perfectField` — Q: [BGR] 4.3/1–2 (`bgr-4.md:126–127`, `:134–138`):
  *"An integral domain `A` is called Japanese if the integral closure of `A` in any finite extension
  of `K` is always a finite `A`-module. … Since each algebraic extension of a perfect field is
  separable, we immediately deduce from the result of DEDEKIND (Theorem 4.2/1) **Proposition 2.**
  Each normal Noetherian integral domain `A`, whose field of fractions is perfect, is Japanese."* M:
  literal; `IsJapaneseRing` is the definition 4.3/1 with the extension `L` given as an
  `A`- and `FractionRing A`-algebra with a scalar tower. D: `IsIntegralClosure.finite` (Dedekind's
  theorem 4.2/1 in Mathlib: `[IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegrallyClosed A] [IsNoetherianRing A]`, signature in `names_mathlib4.out`),
  `integralClosure.isIntegralClosure`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`. A: [1]
  BGR's counterexample without perfectness (`bgr-4.md:140–141`, F. K. Schmidt) — hypothesis necessary
  ✓. [2] `L = FractionRing A`: the integral closure is `A` ✓. [3] the definition quantifies over
  `L : Type u`; every finite extension is isomorphic to one in that universe. [5] three lemmas.
  SURVIVED. Internal node: the definition `IsJapaneseRing` — [6] it is a `Prop` on the domain alone
  (no choice of fraction field: `FractionRing A`), as [RM] convention 3 prefers predicates ✓.

---

## G18 — The Tate algebra in characteristic zero (`TateAlgebra/Stable.lean`), [RM] §0.4.2–§0.4.3

- **L18.1** `isWeaklyStable_fractionRing` — Q: [BGR] 5.3.1/1 `bgr-5.3.1.md:38–41` *"**Theorem 1.** The
  field of fractions `Q(Tₙ)` is weakly stable. Proof. All valued fields of characteristic 0 are
  weakly stable (see Proposition 3.5.1/4). Therefore we have only to consider the case where
  `char k = p > 0`."* M: the first sentence of the proof: the statement for `[CharZero K]`. D: L16.4,
  with the normed-field structure of L16.6–L16.10 on `FractionRing (TateAlgebra K n)`, L1.4 and
  Mathlib's `IsFractionRing.charZero`, `PerfectField.ofCharZero`. A: [6] compiled against the skeleton
  in `scratch/spot5.lean` ✓. [1] characteristic `p`: not claimed (see "Unticketed sub-tree"). [3]
  completeness of `K` is not needed and was removed (`omit [CompleteSpace K]`, D10): the statement
  holds for restricted power series over any nonarchimedean field of characteristic zero. SURVIVED.
- **L18.2** `isJapaneseRing` — Q: [BGR] 5.3.1/3 `bgr-5.3.1.md:89–92` *"**Theorem 3.** `Tₙ` is
  Japanese. Proof. `Tₙ` is a normal Noetherian integral domain (see (5.2.6)). Therefore the assertion
  follows from Proposition 4.3/2 if `char k = 0`"*. M: the case `char k = 0`. D: L17.1 with L11.2,
  L11.3 (normality by `inferInstance`), L1.5, L1.4. A: [6] compiled in `spot5.lean` ✓. [3]
  completeness of `K` is needed (L11.2). SURVIVED.

---

## G19 — Examples (`TateAlgebra/Examples.lean`), [RM] Layer 0, Examples

[RM]: *"`T₀ = K`; `T₁` with `|X|` and the Gauss norm of `1 + pX` over `ℚ_p`; the reduction of
`p + X + pX²` is `X`; the automorphism `X₁ ↦ X₁ + X₂^t` making `X₁ − X₂` distinguished in `X₂`; the
Weierstrass polynomial `X₂² − pX₁X₂ − p` over `T₁ = ℚ_p⟨X₁⟩` with `T₂/(ω)` free of rank `2`; the
maximal ideal `(X₁ − a, X₂ − b)` for `a, b ∈ 𝒪_K` and a maximal ideal of `T₁` whose residue field is
a quadratic extension; `Q(T₁)` is not complete."* Each example is a statement about named objects,
so the "source" is the roadmap sentence; the proofs are applications of G1–G11. `T₀ ≃+* K` is
complete in the skeleton ([SEAM] `isEmptyEquiv`).

- **L19.1** `norm_X` — the roadmap's "`|X|`". D: [SEAM] `Restricted.norm_X`, `norm_one`. SURVIVED
  ([2] `n = 0`: vacuous; [5] one lemma).
- **L19.2** `not_isMulDistinguishedX0_X_one`, **L19.3** `isMulDistinguishedX0_shear_X_one` — the
  roadmap's chart example. ⚠ The roadmap's series `X₁ − X₂` is already `X₂`-distinguished of order
  one (its coefficient of `X₂` is the unit `−1`), so it does not illustrate anything; the board uses
  the variable that is *not* the distinguished one, which is distinguished of no order, and becomes
  distinguished of order one after the shear (erratum E12). D: L7.8 (`X 1 = ofTail (X 0)`),
  [TOWER] `isMulDistinguishedX0_iff`, `coeffX0_ofPolynomial`, the forward half of L2.16 (the variable
  of `T₁` is not a unit), `not_isUnit_zero`; L9.11, L7.7, L7.17, L7.21 for the polynomial
  `X + C (X 0)`. A: [2] every order `s` is excluded, including `s = 0` ✓. SURVIVED.
- **L19.4** `isMaximal_ker_aeval` — the roadmap's rational point. M: the kernel of the evaluation at
  a point of `(K⁰)ⁿ` is maximal; that it is generated by the `X i − x i` is [BGR] 7.1.1/3 (Layer 3)
  and is not claimed. D: L5.3 with `L = K`. SURVIVED.
- **L19.5** `norm_one_add_p_mul_X`, **L19.6** `isUnit_one_add_p_mul_X` — D: `Padic.norm_p`
  (⚠ `padicNormE.norm_p` no longer exists), `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`,
  [SEAM] `norm_C`, `norm_X`, `norm_mul`; `isUnit_one_sub_of_norm_lt_one` or L2.16. SURVIVED.
- **L19.7** `reduction_p_add_X_add_p_mul_X_sq` — D: `map_add`, `map_mul`, `map_pow` of `reduction` on
  the subring elements, the reductions of a constant of norm `< 1` (L2.6) and of a variable. A: [2]
  the hypothesis `h` (norm `≤ 1`) is an argument only so that the statement can name the element of
  `T⁰`; it is true and provable, and the example does not depend on its proof term. SURVIVED.
- **L19.8** `isWeierstrassPolynomial_example` — D: L7.17, `Polynomial.monic_X_pow_sub`, coefficient
  norms from `Padic.norm_p` and `norm_X`. SURVIVED.
- **L19.9** `isMaximal_span_X_sq_sub_p` — the roadmap's quadratic point: `(X² − p) ⊂ T₁` over `ℚ_p`.
  D: L7.17 (`X² − p` is a Weierstrass polynomial over `T₀`), L8.2 and `RingEquiv.ofBijective`,
  `Polynomial.mapEquiv` along `isEmptyEquiv`, irreducibility of `X² − p` over `ℚ_p`
  (`Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`; no root because
  `Padic.norm_eq_zpow_neg_valuation` makes `‖a‖² = p⁻¹` impossible),
  `PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.map_isMaximal_of_equiv`, `MulEquiv.isField`,
  `Ideal.Quotient.maximal_of_isField`. A: [1] `p = 2`: `X² − 2` is still irreducible over `ℚ₂` by
  the same valuation argument ✓. [5] the longest example — a ticket shared only with L19.8.
  SURVIVED.

---

## Unticketed sub-tree: §0.4 in characteristic `p`

[RM] §0.4.2–§0.4.3 ask for weak stability of `Q(Tₙ)` and Japaneseness of `Tₙ` over every complete
nonarchimedean field. The board delivers them in characteristic zero (G18), together with the
general statements they follow from (G16, G17). In characteristic `p` the source's proof is the
following chain, **transcribed in `references/` but not stated in Lean and not ticketed**:

- [BGR] 5.3.1/2 (`bgr-5.3.1.md:45–83`): *"Each `Tₙ`-submodule of finite rank in `Tₙ^{p⁻¹}` is
  b-separable"*, proved through `(k⟨X⟩)^{p⁻¹} = k^{p⁻¹}⟨Y⟩`, the smallest complete subfield
  `k′ ⊂ k^{p⁻¹}` containing finitely many coefficient sequences, *"`k′` is a `k`-vector space of
  countable type. Any such vector space is b-separable by Proposition 2.7.1/2. Therefore `k′⟨Y⟩` is a
  b-separable `k⟨Y⟩`-module by Corollary 2.2.6/5"*, the norm-direct decomposition
  `k⟨Y⟩ = ⊕ k⟨X⟩ Y^ν`, and normality of `k′⟨Y⟩`.
- [BGR] 3.5.3/1–2 (`bgr-3.5.md:101–135`): `K` is weakly stable iff `K^{p⁻¹}` is weakly
  `K`-cartesian (induction over `K_n = K^{p^{−n}}`, the Frobenius homeomorphism, the perfect closure,
  transitivity 3.2.2/4, towers 2.3.3/2), and the criterion for `K = Q(A)` through 2.3.3/3.
- [BGR] 4.1/3–4, 4.3/3, 4.4/2 (`bgr-4.md:62–85`, `:144–154`, `:182–201`): tame modules and the first
  and third criteria for Japaneseness.

API gaps, none of which exists in Mathlib or in this chain:

| Gap | Content | Source |
|---|---|---|
| AG1 | b-separable normed modules; stability under `b(∏)`, `c(∏)`, `⊕` | 2.2.5/1–4, `bgr-2.md:11–38` |
| AG2 | the functor `M ⇝ T(M)` of strictly convergent series with coefficients in a normed module | 2.2.6/1–8, `bgr-2.md:42–98` |
| AG3 | weakly cartesian spaces in general (2.3.2/1 equivalences, 2.3.3/1–3), and spaces of countable type are b-separable (2.6.1–2.6.2, 2.7.1/2: `α`-cartesian bases) | `bgr-2.md:151–215`, `:246–341` |
| AG4 | the valued field `K^{p⁻¹}` and the ring `A^{p⁻¹}`, with the Frobenius as a homeomorphism; `Tₙ^{p⁻¹} = k^{p⁻¹}⟨Y⟩` | `bgr-3.5.md:98–131`, `bgr-5.3.1.md:47–58` |
| AG5 | 3.5.3/1–2 (the criterion) | `bgr-3.5.md:101–135` |
| AG6 | tame modules and the criteria 4.3/3, 4.4/1–2 | `bgr-4.md:41–201` |

Why it is not on this board: (i) the confidence gate fails — AG3 is the `p`-adic functional analysis
roadmap's §2.2 and §2.4 (orthogonal bases over fields, countable type), whose Lean shape is not yet
fixed, and AG4 has no agreed Lean shape at all (Mathlib's `PerfectClosure` is abstract and carries
no norm); (ii) it is Part A of BGR, six definitions and roughly as many statements as the rest of
this board; (iii) nothing else on the board depends on it, and its consumers are [RM] §1.2.5 and
§2.4.1 only. It is declared in `Stable.lean`'s docstring and in the plan, and is the natural content
of a board of its own.

---

## Gate (Step 5)

1. **Every leaf is discharged or is a declared API gap.** 205 open declarations in 19 groups; each
   has a discharge line naming Mathlib lemmas (verified by elaboration, 0 errors), floor or chain
   declarations (verified, 0 errors; all sorry-free), or earlier leaves. The only API gaps
   are AG1–AG6 above, which belong to the unticketed sub-tree and to no ticket. ✓
2. **The skeleton compiles.** `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples`:
   `Build completed successfully (2722 jobs)`, `sorry` warnings only. ✓
3. **Every leaf has a verbatim source quote and a match paragraph.** [BGR] and [Bo] quotes carry a
   line locator into `references/`; glue leaves (L1.3–L1.4, L4.1, L7.6–L7.12, L10.2, L19.*) quote the
   source sentence or roadmap clause they implement and say so. ✓
4. **Every leaf and every internal node passed the adversarial pass**, with at least three attack
   categories recorded per leaf (grouped leaves share one block). Ten defects were found and
   repaired in the skeleton (table above); no recorded attack is left open. ✓
5. **Prior-B2 log consulted**: no name match; eight defect shapes applied (table above). ✓
6. **The tree mirrors the sources.** Internal nodes N1–N16 cite the source's own statement. Declared
   deviations from a source's *proof*, each with the source passage that licenses it: N6 (roots of
   unity in place of Lemma 3.4.1/4), L5.6 (Bosch's unit argument in place of BGR's residue norm),
   L10.6 (Mathlib's integral-extension lemma for the last third of BGR's proof), L10.9–L10.10
   (Bosch's descent in place of BGR 7.1.1/3), G15 (Bosch 1.3 in place of BGR 5.2.7). No size
   estimates are given anywhere in this document. ✓
7. **Statement shape**: no top-level conjunction after D8; exceptions listed above. ✓

No leaf is REVIEW-PENDING. **Verdict: the gate passes for G1–G19.** The characteristic-`p` half of
[RM] §0.4.2–§0.4.3 is outside the gate and outside the ticket board, and is flagged to the user.
