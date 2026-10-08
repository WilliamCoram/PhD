# Plan — Tau Ceti RigidAnalyticGeometry Layer 2: the supremum seminorm and the reduction

Board: `.mathlib-quality/tauceti-rag-layer2/` (named; always pass the path). Planned 2026-10-06.
Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md` §2.1–§2.5 + Examples (lines 733–841).
Floor: Layer 0 (`tauceti-rag-layer0`, sorry-free) and Layer 1 (`tauceti-rag-layer1`, sorry-free).
Build: `~/.elan/bin/lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>`; never `lake build PhD`;
never `import PhD.Main.*`; one Lean process at a time.

## 1. Goal (the milestone statements, in Lean)

M1 (BGR 3.8.1/7(a), §2.1.4) `Affinoid.supSeminorm_eq_supSpectralValue_minpoly`:
  for `φ : B →ₐ[K] A` with `B` an integrally closed domain, `Algebra.IsIntegral B A`, `A` torsion-free
  over `B` (`Module.IsTorsionFree B A` after `letI := φ.toAlgebra`), both `HasSupSeminorm`,
  `supSeminorm K f = supSpectralValue K (minpoly B f)`.
M2 (BGR 6.2.1/4(i), §2.2.1) `IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`:
  `A ≠ 0` affinoid, `f : A` ⊢ `∃ x : MaximalSpectrum A, evalNorm K x f = supSeminorm K f`.
M3 (BGR 6.2.3/1, 6.2.3/3, §2.3.1, §2.3.3) `IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`
  and `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun` (`|f|_sup = inf ‖fⁱ‖^{1/i}`).
M4 (BGR 6.2.4/1, §2.4.1) `IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm` (`[CharZero K]`):
  `A` reduced affinoid Banach ⊢ `∃ C, ∀ f, ‖f‖ ≤ C * supSeminorm K f`.
M5 (BGR 6.3.1/6, §2.5.3) the three implications of Theorem 6 for `B` reduced:
  `isometry_of_injective_isStrict`, `injective_reductionMap_iff_isometry`, `isStrict_of_isometry`.

## 2. References (transcriptions in `references/`)

[BGR] Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*: `bgr-6.2-6.3.1.md` (§6.2.1–6.2.4, §6.3
intro, §6.3.1, pp. 236–245), `bgr-3.8.md` (statements 3.8.1/1–9, 3.8.2/1–6, 3.8.3/1–4; Layer 0
copy), `bgr-3.8-proofs.md` (proofs of 3.8.1/7–9, 3.8.2/3–6, 3.8.3/1–7, pp. 171–182),
`bgr-4-and-3.8.3.7.md` (3.8.3/7 + ch. 4), `bgr-3.7.md` (3.7.2/1–2, 3.7.3/1–5, 1.2.4, 1.2.5),
`bgr-1.3-1.5.md` (1.2.5/6–8, 1.3.1/1–5, 1.3.2/1, 1.5.1/1, 1.5.3/1, 1.5.4/1).
[Bo] Bosch, *Lectures on Formal and Rigid Geometry*, §1.4 (`bosch-lectures.txt`, Props 12–19 at
lines ≈1100–1440; secondary source for 6.2.1/4, 6.2.2/4, 6.2.3/1–2).
[L0]/[L1] the Layer 0/1 code under `PhD/TauCeti/Code/`.

## 3. Conventions carried over (roadmap §0 conventions 3–5; Layer 0/1 API)

* Points are `MaximalSpectrum A`; `Affinoid.evalNorm K x f := spectralValue (minpoly K (mk x f))`;
  `Affinoid.supSeminorm K f := ⨆ x, evalNorm K x f` (a real `iSup`, junk `0` when unbounded or
  empty). Both live in `SupSeminorm.lean` with `variable (K) [NormedField K] {A} [CommRing A]
  [Algebra K A]`.
* An affinoid algebra carries NO topology (`IsAffinoidAlgebra K A : Prop`). Every statement that
  mentions a norm on `A` takes `[NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A] [NormOneClass A]` ("a complete `K`-algebra norm", roadmap convention 3).
* Power-bounded = `PowerBounded.IsPowerBounded` (PFA `PowerBounded.lean`), topologically
  nilpotent = Mathlib `IsTopologicallyNilpotent`; the subring `Subring.unitClosedBall` and the ideal
  `NormedRing.openUnitBallIdeal` of PFA `UnitBall.lean` are the norm-side unit balls.
* Spectral value of a monic polynomial over a seminormed ring: Mathlib `spectralValue` (for a norm)
  — for the sup seminorm we define `supSpectralValue` directly (§5.2).

## 4. Mathlib inventory (verified by elaboration 2026-10-06 against pin bbc4475e)

`spectralValue`, `spectralValue_X_pow`, `spectralValue_nonneg`, `max_norm_root_eq_spectralValue`
(needs `IsPowMul f`, `IsNonarchimedean f`, `f 1 = 1`, a splitting `mapAlg K L p = ∏ (X - C a)`),
`spectralNorm.normedField K L`, `spectralNorm.normedAlgebra' K E L`, `spectralNorm.completeSpace`,
`spectralNorm_unique`, `spectralAlgNorm_isPowMul`, `isNonarchimedean_spectralNorm`,
`NormedAlgebra.norm_eq_spectralNorm` (used by [L0] `evalNorm_eq_norm_algHom`);
`minpoly.algHom_eq`, `minpoly.isIntegrallyClosed_eq_field_fractions'` (needs `[IsIntegrallyClosed R]
[IsDomain S] [Module.IsTorsionFree R S]` via the `NoZeroSMulDivisors`-free spelling),
`minpoly.ker_eval` (same hypotheses: `RingHom.ker (aeval s) = span {minpoly R s}`),
`minpoly.monic`, `minpoly.aeval`, `minpoly.ne_zero`, `minpoly.dvd`;
`AdjoinRoot.quotEquivQuotMap`, `AdjoinRoot.liftAlgHom` (NOT `liftHom`), `AdjoinRoot.mk`,
`AdjoinRoot.algebraMap_eq`; `Polynomial.SplittingField`, `SplittingField.splits`,
`Splits.eq_prod_roots_of_monic`, `Polynomial.scaleRoots`, `monic_scaleRoots_iff`,
`scaleRoots_aeval_eq_zero`, `coeff_scaleRoots`;
`Ideal.comap_isMaximal_of_surjective`, `Ideal.map_eq_top_or_isMaximal_of_surjective`,
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, `Ideal.exists_ideal_over_maximal_of_isIntegral`,
`Ideal.comap_lt_comap_of_integral_mem_sdiff`, `Ideal.IsMaximal.isClosed` (NormedRing +
`HasSummableGeomSeries`), `Ideal.Quotient.algebraQuotientOfLEComap`, `Algebra.IsIntegral.quotient`;
`minimalPrimes.finite_of_isNoetherianRing`, `Ideal.sInf_minimalPrimes` (`sInf I.minimalPrimes =
I.radical`), `Ideal.exists_minimalPrimes_le`, `nilradical`, `IsReduced`, `IsJacobsonRing.out`
(`I.IsRadical → I.jacobson = I`), `Ideal.jacobson`, `Ideal.radical`;
`smoothingFun` (abbrev `⨅ n : ℕ+, μ (x ^ n) ^ (1 / (n : ℝ))` for `μ : RingSeminorm R`),
`SeminormedRing.toRingSeminorm`, `smoothingSeminorm` (`IsNonarchimedean μ` → RingSeminorm),
`smoothingFun_le`, `smoothingFun_isPowMul`, `tendsto_smoothingFun_of_ne_zero` (check at ticket
time: names in `Mathlib/Analysis/Normed/Unbundled/SmoothingSeminorm.lean`);
`IsLocalization.exist_integer_multiples_of_finset`, `IsFractionRing.injective`,
`exists_linearIndependent`, `Module.Finite.of_surjective`, `Submodule.fg_top`,
`LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero`;
`ContinuousLinearMap.exists_preimage_norm_le` (open mapping, used by [L1] `Noetherian.lean`),
`LinearMap.continuous_of_finiteDimensional`, `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`,
`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`;
`Pi.normedCommRing`, `Pi.normedAlgebra` (sup norm on `ι → A`; NO `IsUltrametricDist` instance for
Pi types in Mathlib — a local instance is a ticket), `Pi.completeSpace`.
Absent from Mathlib (become project lemmas): a product bound for `spectralValue` (BGR 1.5.4/1);
`IsUltrametricDist (ι → A)`; `TauCeti.Huber.IsUniform` (not in this repository: seam note §7).

## 5. API design

### 5.1 `Affinoid.HasSupSeminorm K A : Prop` (class) — BGR's `Max_k A` + finiteness, as a class
```
class HasSupSeminorm (K A) [NormedField K] [CommRing A] [Algebra K A] : Prop where
  isAlgebraic : ∀ x : MaximalSpectrum A, Algebra.IsAlgebraic K (A ⧸ x.asIdeal)
  bddAbove : ∀ f : A, BddAbove (Set.range fun x : MaximalSpectrum A ↦ evalNorm K x f)
```
Why: BGR 3.8.1 works with `Max_k A` (the `k`-algebraic maximal ideals) and `|f|_sup = ∞` is
allowed; our `supSeminorm` is a real `iSup` over ALL maximal ideals. `evalNorm` is `0` at a
transcendental point (minpoly `= 0`), so submultiplicativity fails there, and the `iSup` is junk
when unbounded. For affinoid algebras both fields hold (Layer 1 `finiteDimensional_quotient_of_isMaximal`
+ Layer 0 `supSeminorm_le_norm` through a presentation): instance
`IsAffinoidAlgebra.hasSupSeminorm`. For Banach `A` whose residue fields are algebraic the second
field is `bddAbove_range_evalNorm` [L0]. Everything in §2.1 is stated for `[HasSupSeminorm K A]`.

### 5.2 `supSpectralValue K (q : B[X]) : ℝ := ⨆ i : Fin q.natDegree, supSeminorm K (q.coeff i) ^ (1 / (q.natDegree - i : ℝ))`
the spectral value `σ(q) = max |b_i|_sup^{1/i}` (BGR 1.5.4) of a monic `q` for the SEMInorm
`|·|_sup` (Mathlib's `spectralValue` needs a `NormedRing`, so it is unusable for a seminorm). Same
shape as Mathlib's `spectralValueTerms`. Lemmas: `supSpectralValue_nonneg`, `le_supSpectralValue`
(`supSeminorm K (q.coeff i) ≤ σ(q) ^ (natDegree - i)`), `supSpectralValue_eq_spectralValue` when
`supSeminorm = ‖·‖`, product bound `supSpectralValue_mul_le` (BGR 1.5.4/1, inequality half only),
`supSpectralValue_map_le` (coefficients through a contraction), `supSpectralValue_pow_le`.

### 5.3 `supRingSeminorm K A : RingSeminorm A` (for `[HasSupSeminorm K A]`, 3.8.1/3) packaging
`supSeminorm` with `IsPowMul`, `IsNonarchimedean`, `supSeminorm_smul`; feeds `smoothingFun` and
`max_norm_root_eq_spectralValue`-style arguments. Also `supSeminorm_le_max`, `supSeminorm_mul_le`,
`supSeminorm_pow`, `supSeminorm_one_le`, `supSeminorm_zero`, `supSeminorm_neg`.

### 5.4 The core fibre lemma (3.8.1/7(a) at one point) — `supSeminorm_adjoinRoot_quotient`
For a monic `q : B[X]` and `y : MaximalSpectrum B` with `B ⧸ y` finite over `K`: the sup seminorm
of the class of `X` in `(B ⧸ y)[X] ⧸ (q̄)` equals `spectralValue q̄` (computed in the normed field
`B ⧸ y` given the spectral norm). Route: maximal ideals of `(B⧸y)[X]⧸(q̄)` ↔ monic irreducible
factors `p` of `q̄`; at `p`, `evalNorm = ‖root of p‖` in a splitting field `E` of `q̄` normed by
`spectralNorm.normedField K E` (+ `normedAlgebra' K (B⧸y) E`); `max_norm_root_eq_spectralValue`
over the roots of `q̄` gives `σ(q̄) = max_{roots} ‖a‖ = max_p (max over roots of p) = max_p
evalNorm`. Then 3.8.1/7(a): `≤` is 6.2.2/3-style (`le_supSpectralValue_of_aeval_eq_zero`), `≥` is
`sup_y σ(q_y) = σ(q)` (coefficientwise MMP-free: `|b_i|_sup = sup_y |b_i(y)|`) + the fibre lemma
through `AdjoinRoot.quotEquivQuotMap` (`A ≅ B[X]/(q)` by `minpoly.ker_eval`, then `A ⧸ yA ≅
(B⧸y)[X]⧸(q̄)`) and `evalNorm` is monotone along `A → A ⧸ yA` (contraction 3.8.1/4) with every
`x ∈ Max A` over some `y`.

### 5.5 Affinoid layer (`Affinoid/*.lean`, hypotheses `hA : IsAffinoidAlgebra K A`)
* 6.2.1/4(i) MMP: domain case = Noether normalisation `T_d ↪ A` ([L1] `exists_finite_injective`)
  + 3.8.1/7(b) (index attaining the max in `σ(q)` + Layer 0 `exists_evalNorm_eq_norm` on `T_d` +
  the fibre-lemma point `x` over `y`); general case through minimal primes `π_i : A → A ⧸ 𝔭_i`
  (3.8.1/5 `supSeminorm_eq_iSup_minimalPrimes`, finite by noetherianity).
* 6.2.1/4(ii): value group — `exists_smul_pow_supSeminorm_eq_one`; the uniform `m` is the index
  bound `Module.finrank` of the Noether normalisation fibre: stated as
  `exists_forall_exists_smul_pow_supSeminorm_eq_one` (`∃ m, ∀ f, supSeminorm f ≠ 0 → ∃ c, |c f^m| = 1`).
* 6.2.1/4(iii): `supSeminorm_eq_zero_iff_isNilpotent` via `IsJacobsonRing` ([L1]) and 3.8.1/9.
* 6.2.1/5: `AlgHom.continuous_of_isReduced_of_isAffinoidAlgebra` via [L1]
  `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional` with `𝔅 = {𝔪 | IsMaximal}`
  (`Ideal.IsMaximal.isClosed` on both sides; `sInf = ⊥` by Jacobson + reduced).
* 6.2.2/4: `exists_monic_aeval_eq_zero_supSeminorm_eq_supSpectralValue` (domain: composite
  `T_d → B → A`; general: `q := (∏ q_i)^e` + product bound + 3.8.1/5).
* 6.2.3: `powerBounded K A : Subring A := {f | supSeminorm K f ≤ 1}`,
  `topologicallyNilpotent K A : Ideal (powerBounded K A)`, `Reduction K A := powerBounded ⧸
  topologicallyNilpotent` (a `K̃`-algebra: `Algebra (ResidueField (unitClosedBall K)) (Reduction K A)`),
  `isPowerBounded_iff_supSeminorm_le_one`, `isTopologicallyNilpotent_iff_supSeminorm_lt_one`,
  `supSeminorm_eq_smoothingFun`, `reductionEquiv_tateAlgebra` (`Reduction K (T_n) ≃+* K̃[X]`
  from [L0] `reductionEquiv`), 6.2.3/5 both directions as two lemmas, uniformity lemmas.
* 6.2.4/1 (`[CharZero K]`): domain case = `BanachFunctionAlgebra.exists_norm_le_mul_supSeminorm_of_finite`
  (3.8.3/7, domain `A` only, §6 deviation D1); reduced case through `A ↪ ∏ᵢ A ⧸ 𝔭ᵢ`.
* §2.5: `powerBoundedMap φ`, `reductionMap φ : Reduction K B →+* Reduction K A`, `IsStrictMap`,
  6.3.1/1–6, Examples 1–2.

### 5.6 `BanachAlgebra/Module.lean`: closed submodules of finite modules (BGR 3.7.2/2, 3.7.3/1)
Module version of [L1] `Ideal.isClosed_of_isNoetherianRing`: for a noetherian Banach algebra `B`
and `n`, every `B`-submodule of `Fin n → B` is closed (`Submodule.isClosed_of_isNoetherianRing`),
hence every submodule of a finite normed `B`-module with the quotient/product topology is closed.
Needed by 3.8.3/7 (closedness of `A` in `B^n`) and by 6.2.4/1's reduced case.

## 6. File structure and dependency graph (all under `PhD/TauCeti/Code/RigidAnalyticGeometry/`)

```
SupSeminorm/Seminorm.lean      HasSupSeminorm, supRingSeminorm, 3.8.1/3 (a)–(f), 3.8.1/4 contraction,
                               3.8.1/9, supSeminorm along quotients, iSup over minimal primes 3.8.1/5
  ← SupSeminorm.lean [L0], Affinoid/Noether.lean [L1] (for the affinoid instance), NormedQuotient [L1]
SupSeminorm/SpectralValue.lean supSpectralValue + 1.5.4/1 bound + 6.2.2/3 (le_supSpectralValue_of_aeval_eq_zero)
  ← SupSeminorm/Seminorm
SupSeminorm/Integral.lean      3.8.1/6 (a)(c) isometry, fibre lemma, 3.8.1/7 (a)(b)(c)(d), 3.8.1/8
  ← SupSeminorm/SpectralValue, TateAlgebra/MaxModulus [L0] (only for examples: NOT imported here)
SupSeminorm/Banach.lean        3.8.2/3 continuity, 3.8.2/4 equivalence, 3.8.2/5, 3.8.2/6
  ← SupSeminorm/Integral, BanachAlgebra/Continuity [L1], PFA PowerBounded
BanachAlgebra/Module.lean      3.7.2/2 (module), 3.7.3/1: submodules of Bⁿ closed, finite modules
  ← BanachAlgebra/Noetherian [L1]
SupSeminorm/FunctionAlgebra.lean 3.8.3/1–4 (as norm statements), 3.8.3/7 (domain case)
  ← SupSeminorm/Banach, BanachAlgebra/Module, WeaklyStable [L0]
Affinoid/SupSeminorm.lean      instance HasSupSeminorm, 6.2.1/1,3,4(i)(ii)(iii),5; 6.2.2/1,2,4
  ← SupSeminorm/Integral, Affinoid/Noether [L1], Affinoid/Continuity [L1], TateAlgebra/MaxModulus [L0]
Affinoid/PowerBounded.lean     6.2.3/1,2,3; powerBounded subring; uniformity
  ← Affinoid/SupSeminorm, SupSeminorm/Banach
Affinoid/Reduction.lean        Reduction, K̃-algebra, 6.2.3/4,5, T_n case
  ← Affinoid/PowerBounded, TateAlgebra/Reduction [L0]
Affinoid/FunctionAlgebra.lean  6.2.4/1 (domain, reduced), §2.3.5 uniformity, §2.4.3 consequences
  ← Affinoid/PowerBounded, SupSeminorm/FunctionAlgebra, TateAlgebra/Stable [L0]
Affinoid/ReductionFunctor.lean powerBoundedMap, reductionMap, IsStrictMap, 6.3.1/1–6
  ← Affinoid/Reduction, Affinoid/FunctionAlgebra
Affinoid/SupExamples.lean      the roadmap Examples
  ← Affinoid/ReductionFunctor, Affinoid/Examples [L1]  (chain root imports this file: gate ticket)
```
Namespaces: `Affinoid` for the seminorm API (`Affinoid.supSeminorm`, `Affinoid.supSpectralValue`,
`Affinoid.HasSupSeminorm`, `Affinoid.powerBounded`, `Affinoid.Reduction`), `IsAffinoidAlgebra.*`
for the affinoid theorems (dot notation on `hA`), `AlgHom.*` for continuity/isometry statements.

## 7. Seam notes
* `TauCeti.Huber.IsUniform` (roadmap §2.3.5, adic §4.2) does not exist in this repository; the
  uniformity statements are proved in their norm form (`powerBounded` bounded ⇔ `∃ C, ‖f‖ ≤ C *
  supSeminorm`), and the `IsUniform` bridge is a one-line seam ticket when that roadmap lands.
* `TateAlgebra K n` is an `abbrev` for `Restricted K (1 : Fin n → ℝ)`; cross the subtype seam with
  term steps, never `rw` ([[restricted-seam-convention]]); pin `(S := TateAlgebra K n)` when needed.
* `evalNorm` at a transcendental point is `0`: every lemma about `evalNorm` of a product/sum needs
  the algebraic hypothesis (`HasSupSeminorm.isAlgebraic`) or `[FiniteDimensional K (A ⧸ x.asIdeal)]`.
* PFA `IsPowerBounded.map` on quotients: make the ideal and the index explicit (Layer 1 trap).

## 8. Deviations from the roadmap / from BGR (recorded, not silently absorbed)

D1 **3.8.3/7 only for `A` a domain.** BGR's proof decomposes `Q(A)` into a product of fields by
   Dedekind's lemma 3.1.4/1 and takes the spectral norm on the product. We prove the domain case
   (`A` a domain, finite injective over `B`) by the coordinate route (§5.5), and obtain BGR 6.2.4/1
   for reduced affinoid `A` from the domain case through `A ↪ ∏ A ⧸ 𝔭ᵢ` exactly as BGR does on
   p. 242. The general reduced-`A` form of 3.8.3/7 (roadmap §2.4.2, "`A` a finite torsion-free
   `B`-algebra which is reduced") is NOT formalised; its only consumer in the roadmap is 6.2.4/1,
   which is covered. The final statement of 3.8.3/7 as a norm inequality `∃ C, ∀ f, ‖f‖ ≤ C *
   supSeminorm K f` carries no `SupNormed` type synonym (D3).
D2 **`[CharZero K]` on 6.2.4/1 and its consequences** (§2.3.5 uniformity ⇒, §2.4.3, 6.3.1/6 (ii)⇒(i)):
   Layer 0 proves weak stability of `Q(T_d)` only in characteristic 0
   (`Affinoid.TateAlgebra.isWeaklyStable_fractionRing` needs `[CharZero K]`; BGR 5.3.1/1 is
   characteristic-free but Layer 0 took the perfect-field route). Statements are parametrised by
   `(hws : IsWeaklyStable (FractionRing (TateAlgebra K d)))` where cheap, and the affinoid
   headline takes `[CharZero K]`.
D3 **No completeness statement for `|·|_sup`** ("`|·|_sup` is a complete norm on `A`"): putting a
   second `NormedRing` structure on `A` needs a type synonym; instead we prove the equivalence of
   norms `supSeminorm ≤ ‖·‖ ≤ C * supSeminorm`, which is the form every later consumer uses
   (Banach function algebra ⇔ equivalence, BGR 3.8.3/2).
D4 **Counterexample `K⟨X,Y⟩/(XY − c)`**: we prove `|f₁|_sup = 1 = |f₂|_sup` and `|f₁f₂|_sup = |c| < 1`
   (so `|·|_sup` is not multiplicative); the statement "this algebra is a domain" needs the Laurent
   series algebra `k⟨X, X⁻¹⟩` (not in the chain) and is deferred (recorded in `SupExamples.lean`).
D5 **Example 1 (p. 245)** is stated for an arbitrary finite extension `L/K` with residue degree 1 and
   `[L : K] > 1`, as `Function.Bijective (reductionMap (Algebra.ofId K L)) ∧ ¬ Function.Surjective
   (algebraMap K L)`; the instance `ℚ₂(√2)` is not constructed.
D6 **6.2.1/4(ii) uniform `m`**: the roadmap asks for `m` depending only on `A`; we take
   `m := d!`-free form "`m` = the Noether normalisation degree bound" via `exists_forall_exists_…`
   with `m` the lcm of `1..n` for `n` the degree of the normalisation; proved from 3.8.1/7(a).
D7 **Statement shapes**: BGR 6.2.1/4 (i)/(ii)/(iii), 6.2.3/1–2 (iff's), 6.2.3/5 (iff), 6.3.1/6
   (three-way) are split one conclusion per declaration (statement-splitting rule); the bundled
   forms are not stated.
D8 **3.8.1/7 for `A` a domain** (file `SupSeminorm/Integral.lean`): BGR's hypothesis is "`A` torsion-free
   over `B`"; Mathlib's `minpoly.ker_eval` (the identification `B[f] ≅ B[X]/(minpoly)`) needs
   `IsDomain A`, and every Layer 2 consumer (6.2.1/4, 6.2.2/4, 6.2.4/1) reduces to domains through the
   minimal primes exactly as BGR do. The torsion-free reduced case is not stated.
D9 **"`Q(T₁)` is not complete for the Gauss norm"** (roadmap Examples) is not formalised: BGR only
   mention the completion (p. 175) without proof, and nothing downstream consumes it.
D10 **6.2.2/4 for finite `φ`**: BGR state it for integral `φ : B → A`; the proof uses the integral half
   of BGR 6.1.2/1 (ii), of which Layer 1 formalised only the finite half
   (`IsAffinoidAlgebra.exists_finite_injective_comp`). Both consumers (6.2.3/1 through a presentation,
   and 6.2.2/2 through Noether normalisation) are finite. 6.2.2/1's isometry statement keeps "integral".
D11 **`supSeminorm_pow` for `n ≠ 0`**: BGR 3.8.1/3 (f) is for `n ∈ ℕ = {1, 2, …}`; for `n = 0` and the
   trivial ring the equation reads `0 = 1`. Caught at planning (statement-shape check).
D12 **Universes**: `IsBanachFunctionAlgebra.of_finite_domain`, `IsAffinoidAlgebra.isBanachFunctionAlgebra_*`
   and `isStrictMap_of_isometry` put the algebra in the universe of `K` (Layer 0's `IsWeaklyStable`
   quantifies over extensions in one universe; same restriction as Layer 1's `isJapaneseRing`).
