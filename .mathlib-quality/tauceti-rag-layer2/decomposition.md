# Decomposition — Tau Ceti RigidAnalyticGeometry Layer 2 (the supremum seminorm and the reduction)

Written 2026-10-06 by `/develop` (planning only). Sources: [RM] = roadmap README §2.1–§2.5 + Examples
(`PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, lines 733–841); [BGR] = `references/bgr-6.2-6.3.1.md`
(§6.2–6.3.1, pp. 236–245), `references/bgr-3.8.md` + `references/bgr-3.8-proofs.md` (§3.8, pp. 168–182),
`references/bgr-1.3-1.5.md` (§1.3.1–1.3.2, §1.5.1, 1.5.3, 1.5.4), `references/bgr-3.7.md` (§3.7, §1.2.4–1.2.5),
`references/bgr-4-and-3.8.3.7.md`; [Bo] = `references/bosch-lectures.txt` §1.4; [L0]/[L1] = the Layer 0/1 code.
Locators are to those files (section/number and page); every leaf quotes its source verbatim.

**Skeleton location** (all `:= by sorry`, 180 declarations, `lake build …Affinoid.SupExamples` clean):
`PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/{Seminorm, SpectralValue, Integral, Banach,
FunctionAlgebra}.lean`, `BanachAlgebra/Module.lean`, `Affinoid/{SupSeminorm, PowerBounded, Reduction,
FunctionAlgebra, ReductionFunctor, SupExamples}.lean`.

## Prior-B2 consultation (all `.mathlib-quality/*/b2_log.jsonl`, 17 logs read)

| Prior defect | Relevance to this board | Action taken at planning |
|---|---|---|
| Layer 1 T004/T014/T022/T023/T016/T059: **dropped section variables** (a `variable` not mentioned in the statement is silently omitted, changing or falsifying it; in particular "without a nontrivially normed field of scalars Banach open mapping fails") | `BanachAlgebra/Module.lean` (5 theorems never mention `K`), `SupSeminorm/FunctionAlgebra.lean` (`exists_coordinateMap`, `exists_norm_le_mul_norm_coordinateMap`) | `include K in` (Module) and `variable (K) in include K in` (FunctionAlgebra) added; every other statement audited: `K` appears in it or `K` is genuinely irrelevant (pure algebra: T012, T033's lemmas, `minpoly_algebraMap_mul_eq_scaleRoots`, `MaximalSpectrum.isClosed_asIdeal`) |
| Layer 1 T060: a **missing completeness hypothesis** on `K` | the Fibre/MinimalPolynomial sections of `Integral.lean` need `spectralNorm.normedField` (`[CompleteSpace K]`) | `[NontriviallyNormedField K] [CompleteSpace K]` added to those sections (T015–T022) |
| `W001–W003` (jacobs): a real `iSup` whose junk value is `0` made a boundedness statement false | `supSeminorm` is such an `iSup`; `evalNorm` is `0` at transcendental points | the class `HasSupSeminorm` (algebraic residue fields + bounded) guards every submultiplicativity/power statement; `supSeminorm_nonneg` is the only class-free lemma |
| `X-4` (LWX): a normalisation assumed silently (`‖p‖ = 1/p`) | Examples with `p` | examples are stated over an arbitrary `K` with `‖a‖ ≤ 1` / `‖c‖ < 1` hypotheses; nothing assumes `‖p‖ = p⁻¹` |
| `J015/J020`: a definition whose field carried no hypothesis, making a later obligation false | `powerBounded`, `topologicallyNilpotent`, `prodHom` fields | every field is a sorry'd obligation with a sketch (T047, T068); `prodHom`'s field is `‖(c, 0)‖ ≤ 1` from `hc` |

## Statement defects found at planning (statement-shape check) and their repairs

| Declaration | Defect | Repair (in the skeleton) |
|---|---|---|
| `supSeminorm_pow` | false for `n = 0` on the trivial ring (`0 = 1`) | `(hn : n ≠ 0)` (BGR's `n ∈ ℕ` is positive); plan D11 |
| 6.2.2/4 (`exists_monic_eval₂_eq_zero_…`, two statements) | BGR: `φ` integral; the proof needs the integral half of 6.1.2/1 (ii), absent from Layer 1 | stated for `φ.toRingHom.Finite`; plan D10 |
| 3.8.1/7 (a)–(d), 3.8.2/5–6 | BGR: `A` torsion-free; `minpoly.ker_eval` needs `IsDomain A` | `[IsDomain A]` (every consumer reduces to domains); plan D8 |
| `IsBanachFunctionAlgebra.of_finite_domain`, `isBanachFunctionAlgebra_of_*`, `isStrictMap_of_isometry` | `IsWeaklyStable` quantifies in one universe | `A`, `B` in the universe of `K`; plan D12 |
| `exists_evalNorm_eq_supSeminorm` (M2) | the zero ring has no point | `[Nontrivial A]` |
| `isDomain_reduction_of_isValuation` | `Ã` is the zero ring for `A = 0` | `[Nontrivial A]` |
| `supSeminorm_one`, `supSeminorm_algebraMap`, `supSeminorm_natCast` | `|1|_sup = 0` in the trivial ring | `[Nontrivial A]` |

**One conclusion per declaration**: BGR 6.2.1/4 (i)/(ii)/(iii) → T041/T042, T043, T044; 6.2.3/1 (iff: two directions
are `IsPowerBounded.supSeminorm_le_one` + `isPowerBounded_iff_supSeminorm_le_one`); 6.2.3/2 (i)⇔(ii)⇔(iii) → three
lemmas (T049); 6.2.3/5 (iff) → three lemmas (T055); 6.3.1/6 (three-way) → T061 ((ii)⇔(iii)), T063 ((i)⇒(iii)),
T064 ((ii)⇒(i) in two lemmas). Shared-witness existentials (`∃ q, Monic ∧ eval₂ = 0 ∧ sup = σ`) are kept bundled.

## Gate conditions (seven, binding)

1. Every leaf below has a verbatim source quote with a locator — yes (the `Q:` lines).
2. Every leaf has a discharge (Mathlib name verified by elaboration on 2026-10-06, project declaration, or a
   proof sketch in `tickets.md`) — yes (the `D:` lines; names marked "verify" are to be re-checked at ticket time
   by `#check`, they are alternatives not load-bearing).
3. Every leaf survived ≥ 3 attacks — yes (the `A:` lines).
4. Every internal node's composition was attacked — yes (per group).
5. The Lean skeleton builds with sorries only — yes (12 modules, 0 errors, 0 non-sorry warnings, 180 sorries).
6. No API gap requiring multi-week development — yes; the two new infrastructure pieces (the fibre computation
   T017 and the module closedness T029) are each ≤ 1 day and have templates (Mathlib `max_norm_root_eq_spectralValue`,
   Layer 1 `BanachAlgebra/Noetherian.lean`).
7. Deviations from the source are recorded (plan D1–D12), none silently absorbed — yes.

Attack vocabulary used below: **[E]** edge case (trivial ring, `n = 0`, empty spectrum, `f = 0`, `|f|_sup = 0`);
**[H]** hidden hypothesis (does the source assume more than the Lean statement?); **[D]** discharge mismatch (does the
named Mathlib/project lemma have the hypotheses we have?); **[C]** composition (could the children hold and the parent
fail?); **[U]** universe/instance seam; **[S]** source drift (does the quote actually say this?).

---

## G1. `SupSeminorm/Seminorm.lean` — BGR 3.8.1/3–5, 3.8.1/9, 6.2.1/3 (T001–T007)

**Source and prose proof.** BGR 3.8.1/3: "If `| |_sup` is finite, it is a power-multiplicative `k`-algebra semi-norm on
`A`; i.e., one has for all `f, g ∈ A`, `c ∈ k`, `n ∈ ℕ` (a)–(f)" (`bgr-3.8.md:45–52`). The proof is pointwise: each
`|f(x)|` is the spectral norm of the field `A/x`, which is a power-multiplicative nonarchimedean `k`-algebra norm (BGR
3.2), and `sup` preserves the inequalities. 3.8.1/4: contraction via `φ⁻¹(x) ∈ Max_k B` (`bgr-3.8.md:54–62`). 3.8.1/5:
"`|f|_sup = sup_{𝔭 ∈ 𝔐} |π_𝔭(f)|_sup`" (`bgr-3.8.md:64–66`), 6.2.1/3 for noetherian `A`. 3.8.1/9: `⋂ 𝔪 = 0`.

**Leaves.**
- **L1.1–L1.8** `evalNorm_mul_le`, `evalNorm_add_le_max`, `evalNorm_pow`, `evalNorm_smul`, `evalNorm_one`, `evalNorm_neg`,
  `evalNorm_algebraMap`, `evalNorm_eq_zero_iff` — Q: `bgr-3.8.md:26–29` "Since `A/x` is an algebraic extension of `k`, it
  can be provided with the spectral norm derived from the given valuation on `k` (cf. (3.2)). Writing `|f(x)|` for the
  spectral norm of the element `f(x) ∈ A/x`". D: Mathlib `spectralNorm_mul`, `isNonarchimedean_spectralNorm`,
  `isPowMul_spectralNorm`, `spectralNorm_smul`, `spectralNorm_one`, `spectralNorm_neg`, `spectralNorm_extends`,
  `spectralNorm_zero_lt` (all verified by `#check`), after `Ideal.Quotient.field`. A: [E] `n = 0` in `evalNorm_pow`:
  `evalNorm x 1 = 1` since `A ⧸ x` is a field (nontrivial) — fine; [H] `spectralNorm_mul` needs both elements algebraic:
  the instance `Algebra.IsAlgebraic K (A ⧸ x)` supplies it; [D] `Ideal.Quotient.field` is a `def`, not an instance —
  `letI` in each proof (the statements never mention the field structure); [E] `evalNorm_eq_zero_iff` `←` needs no
  algebraicity (Layer 0). SURVIVED.
- **L1.9–L1.14** `supSeminorm_nonneg`, `evalNorm_le_supSeminorm`, `supSeminorm_le_of_forall`, `supSeminorm_zero`,
  `supSeminorm_one_le`, `supSeminorm_one` — Q: `bgr-3.8.md:45–52` (a), (e). D: `Real.iSup_nonneg`, `le_ciSup`, `ciSup_le`,
  `Real.iSup_of_isEmpty`. A: [E] empty spectrum (trivial ring): `supSeminorm_le_of_forall` needs `0 ≤ C` — included;
  `supSeminorm_one` needs `[Nontrivial A]` — included; [D] `le_ciSup` needs `BddAbove` — the class field; [S] BGR's
  `|f|_sup = ∞` case is excluded by the class. SURVIVED.
- **L1.15–L1.23** `supSeminorm_add_le_max`, `_mul_le`, `_pow` (`n ≠ 0`), `_smul`, `_neg`, `_algebraMap`,
  `isNonarchimedean_supSeminorm`, `isPowMul_supSeminorm`, `supRingSeminorm` — Q: `bgr-3.8.md:45–52` (b)–(f);
  `bgr-6.2-6.3.1.md` 6.2.1/1 "is a power-multiplicative `k`-algebra semi-norm". D: L1.1–L1.14 + `max_le_max`,
  `mul_le_mul`, `Real.rpow` lemmas. A: [E] `supSeminorm_pow` at `n = 0`, trivial ring: FALSE as first stated —
  REPAIRED (`hn : n ≠ 0`); [E] `supSeminorm_smul` with `‖c‖ = 0`: both sides `0` — fine; [C] `IsPowMul` requires
  `n ≥ 1` only — matches; [D] `RingSeminorm.add_le'` is `≤ +` not `≤ max`: `max_le_add_of_nonneg`. SURVIVED after repair.
- **L1.24–L1.25** `supSeminorm_eq_zero_iff_forall_mem`, `_iff_mem_jacobson_bot` — Q: `bgr-3.8-proofs.md` 3.8.1/9 "If
  `| |_sup` is a norm on a `k`-algebra `A`, then `⋂_{𝔪 ∈ Max_k A} 𝔪 = (0)`". D: L1.8 + `Ideal.jacobson`, `Ideal.mem_sInf`.
  A: [S] BGR state only one direction; the iff is the pointwise content (`|f(x)| = 0 ↔ f ∈ x`), no drift; [E] trivial ring:
  both sides true; [H] `Max_k A` vs all maximal ideals: identical under the class. SURVIVED.
- **L1.26–L1.28** `isMaximal_comap_of_isAlgebraic`, `evalNorm_comapPoint`, `supSeminorm_map_le` — Q: `bgr-3.8.md:54–62`
  "`φ` induces a `k`-algebra monomorphism `B/φ⁻¹(x) → A/x`. Because `A/x` is an algebraic extension of `k`, its subring
  `B/φ⁻¹(x)` must also be an algebraic extension of `k`. Hence `φ⁻¹(x) ∈ Max_k B`. Then … (*)". D: Layer 0
  `isMaximal_ker_of_isAlgebraic` (same proof), `minpoly.algHom_eq` (verified), Layer 0 `evalNorm_eq_norm_algHom`
  (template). A: [H] does `isMaximal_comap` need `B` to have a sup seminorm? No — only algebraicity of `A ⧸ x`
  (statement has exactly that); [D] `minpoly.algHom_eq` needs an injective `K`-algebra map between the residue fields —
  `Ideal.quotientMap` is injective for `comap`; [E] `B` trivial: then `A` is trivial and there is no `x`. SURVIVED.
- **L1.29–L1.33** `HasSupSeminorm.quotient`, `supSeminorm_mk_le`, `evalNorm_le_supSeminorm_mk`,
  `supSeminorm_mk_eq_of_le_jacobson`, `supSeminorm_mk_nilradical` — Q: `bgr-6.2-6.3.1.md` 6.2.1/3 "The second one follows
  from the fact that the nilradical `rad A` is contained in each maximal ideal of `A`." D: `Ideal.comap_isMaximal_of_surjective`
  (verified), `Ideal.map_eq_top_or_isMaximal_of_surjective` (verified), `Ideal.radical_le_jacobson`, `DoubleQuot`. A: [E]
  `I = ⊤`: `A ⧸ ⊤` is trivial, both sides of `supSeminorm_mk_le` are `0 ≤ …` — fine; `supSeminorm_mk_eq_of_le_jacobson`
  for `I = ⊤ ≤ jacobson ⊥` happens only when `A` is trivial — then both sides `0`; [C] residue fields of `A ⧸ I` at `x̄`
  vs `A` at `x`: isomorphic `K`-algebras, so `evalNorm` agrees via `minpoly.algHom_eq`; [S] BGR's 6.2.1/3 is for the
  nilradical; we generalise to `I ≤ jacobson ⊥` (strictly more general, same proof). SURVIVED.
- **L1.34** `exists_minimalPrimes_supSeminorm_mk_eq` — Q: `bgr-3.8.md:64–66` 3.8.1/5; `bgr-6.2-6.3.1.md` 6.2.1/3 "Since `A`
  is Noetherian, there are only finitely many minimal prime ideals … `|f|_sup = max_{1≤i≤r} |π_i(f)|_sup`". D:
  `minimalPrimes.finite_of_isNoetherianRing`, `Ideal.exists_minimalPrimes_le` (both verified), `Finset.exists_mem_eq_sup'`.
  A: [E] trivial ring: no minimal primes, statement false — `[Nontrivial A]` included; [H] every maximal ideal contains a
  minimal prime: `Ideal.exists_minimalPrimes_le` with `⊥ ≤ x` — yes; [C] `max` attained needs finiteness + nonemptiness —
  both supplied. SURVIVED.

**Internal node (3.8.1/3 ⇒ `supRingSeminorm`).** [C] Could all pointwise facts hold and the sup fail to be a seminorm? Only
through unboundedness or junk `iSup` — excluded by the class. SURVIVED.

## G2. `SupSeminorm/SpectralValue.lean` — BGR 1.5.4, 1.5.4/1, 6.2.2/3 (T008–T011)

**Source and prose proof.** `bgr-1.3-1.5.md` 1.5.4: "`σ(p) := max_{1≤μ≤m} |a_μ|^{1/μ}`"; 1.5.4/1 (proof part (1)): "`|c_λ| ≤
max_{μ+ν=λ} {|a_μ| |b_ν|} ≤ max {σ(p)^μ σ(q)^ν} … `σ(pq) ≤ σ(q) = max{σ(p), σ(q)}`"; 6.2.2/3 (`bgr-6.2-6.3.1.md`): "There
exists an index `j` … `|f|_sup^n ≤ |b_j|_sup |f|_sup^{n−j}`. Then `|f|_sup ≤ |b_j|_sup^{1/j}`."

**Leaves.**
- **L2.1–L2.9** definition lemmas (T008) — Q: 1.5.4 as above and "`σ(X^m) = 0`". D: Mathlib's `spectralValueTerms` lemmas
  (same shapes; verified file `SpectralNorm.lean` lines 95–200). A: [E] `natDegree q = 0` (constants): all terms `0`,
  `σ = 0` — consistent with BGR (degree `≥ 1` assumed there; our statements hold for all `q`); [D] `Real.zero_rpow` needs
  exponent `≠ 0`: `1/(d - n) ≠ 0` for `n < d` — yes; [S] BGR index `μ` counts from the top, ours from the coefficient
  index — the same set of values. SURVIVED.
- **L2.10–L2.12** `supSeminorm_coeff_le_supSpectralValue_pow`, `exists_supSpectralValue_eq`, `supSpectralValue_eq_spectralValue`
  — Q: 1.5.4 "`|a_μ| ≤ σ(p)^μ`" (in 1.5.4/1's proof) and 1.5.4/1 (2) "choose `j` … `|b_j|^{1/j} = σ(q)`". D: `Real.rpow`
  algebra, `Finset.exists_max_image`. A: [E] `exists_supSpectralValue_eq` needs `0 < natDegree` — included; [H] the
  equality with Mathlib's `spectralValue` needs `|·|_sup = ‖·‖` on ALL of `B` — hypothesis `h`; [D] `spectralValue` needs
  `SeminormedRing B` — `NormedCommRing B` in the statement. SURVIVED.
- **L2.13** `supSeminorm_le_supSpectralValue_of_eval₂_eq_zero` — Q: 6.2.2/3 verbatim above. D: L1.15–L1.23 + nonarchimedean
  finite-sum bound. A: [E] `q = 1` (`natDegree 0`): `eval₂ = 1 = 0` forces `A` trivial, `|f|_sup = 0 ≤ 0` — fine; [E]
  `|f|_sup = 0`: trivial; [C] BGR divide by `|f|_sup^{n-j}`: needs `|f|_sup ≠ 0` — handled; [H] 6.2.2/3 is stated for
  affinoid algebras; the proof uses only 3.8.1/3–4, so `HasSupSeminorm` suffices — no drift. SURVIVED.
- **L2.14–L2.17** `supSpectralValue_map_le`, `_mul_le`, `_prod_le_of_forall_le`, `_pow_le` — Q: 1.5.4/1 part (1) verbatim
  above; 6.2.2/4's proof "`|f|_sup = σ(p) ≥ σ(q)`". D: `Polynomial.coeff_mul`, `Monic.natDegree_map`, L1.28. A: [E] `p` or
  `q` constant (`= 1`): `σ = 0`, inequality `0 ≤ max` — fine; [H] monicity is needed for the leading coefficients to be `1`
  (`|1|_sup ≤ 1 = s^0`) — both monic in the statement; [E] empty product: `∏ = 1`, `σ(1) = 0 ≤ C` with `0 ≤ C` — included;
  [S] only the inequality is claimed (the equality cases of 1.5.4/1 are not stated). SURVIVED.

**Internal node (6.2.2/4 uses `σ(q) ≤ max σ(q_i)` for `q = (∏ q_i)^e`).** [C] `pow_le` + `prod_le_of_forall_le` compose to
exactly that; `e = 0` gives `q = 1` with `σ = 0` — then `|f|_sup = 0` by the `≤` direction, consistent. SURVIVED.

## G3. `SupSeminorm/Integral.lean` — BGR 3.8.1/6–8 (T012–T022, M1 = T019)

**Source and prose proof.** 3.8.1/6 (`bgr-3.8.md:68–90`): (a) integral monomorphisms are isometries ("the map `x ↦ φ⁻¹(x)`
from `Max_k A` to `Max_k B` is surjective"), (b) `|f|_sup ≤ max |b_i|_sup^{1/i}` pointwise through 3.1.2/1, (c) finiteness
transfers. 3.8.1/7 (`bgr-3.8-proofs.md`): preliminaries "`A = B[f] ≅ B[X]/(q)`" with `q` the minimal polynomial having
coefficients in `B` (integrally closed); Ad (a): `|f|_sup = sup_y |f̄_y|_sup`, `A/yA = (B/y)[X]/(q_y)`, `|f̄_y|_sup =
max_ν σ(q_ν) = σ(q_y)`, hence `= max_i |b_i|_sup^{1/i}`; Ad (b): the sup over `y` is attained, then one of the finitely
many points over `y`; Ad (c): a nonzero coefficient; Ad (d): the scaled equation. 3.8.1/8: a root of `|k_a|`.

**Leaves.**
- **L3.1–L3.3** going up, comap maximal, algebraic residue fields (T012) — Q: `bgr-3.8.md:76–84` (quoted in T012). D:
  `Ideal.exists_ideal_over_maximal_of_isIntegral`, `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`,
  `Algebra.IsIntegral.quotient`, `Ideal.Quotient.algebraQuotientOfLEComap` (all verified). A: [H] going-up needs
  `ker (algebraMap) ≤ y`: `FaithfulSMul` gives `ker = ⊥`; [D] `exists_ideal_over_maximal_of_isIntegral` returns `Q` with
  `Q.IsMaximal ∧ comap Q = P` — exactly the shape; [U] the `Algebra (B ⧸ comap x) (A ⧸ x)` instance is local
  (`letI`), the statement only mentions `K`-algebraicity. SURVIVED.
- **L3.4–L3.5** `HasSupSeminorm.of_isIntegral`, `.of_isIntegral_of_faithfulSMul` (T013) — Q: `bgr-3.8.md:85–90` (c) and the
  pointwise (b) "Due to Proposition 3.1.2/1, this equation implies `|f(x)| ≤ max |b_i(φ⁻¹(x))|^{1/i} ≤ max |b_i|_sup^{1/i}`".
  D: L1.1–L1.8 pointwise, L1.26–L1.28, L3.1–L3.3. A: [C] circularity: the bound on `A` must not use the class on `A`
  (T010 does) — the ticket proves it pointwise (recorded); [E] `A` trivial: `MaximalSpectrum A` empty, both fields
  trivially true; [H] the first direction needs no injectivity (BGR: "due to (b)") — matches. SURVIVED.
- **L3.6–L3.7** isometry and `sup_y` bound (T014) — Q: `bgr-3.8.md:76–84` (a) and `bgr-3.8-proofs.md` p. 172 "Since each
  `y ∈ Max_k B` is contained in some ideal `x ∈ Max_k A`". D: L1.26–L1.33, L3.1. A: [E] `B` trivial: `A` trivial, both
  sides `0`; [C] `Ideal.map_comap_le` gives `map (comap x) ≤ x` — the right direction for `evalNorm_le_supSeminorm_mk`;
  [H] `supSeminorm_le_of_forall_supSeminorm_mk_map_le` is independent of integrality — fine (noted for `omit`). SURVIVED.
- **L3.8–L3.9** fields (T015) — Q: `bgr-3.8.md:38–40` "if `A` is an algebraic extension of `k`, this definition obviously
  yields the spectral norm on `A`". D: `Ideal.bot_isMaximal`, `minpoly.algHom_eq`. A: [E] a field has exactly one maximal
  ideal — `Ideal.eq_bot_or_top`; [D] `spectralNorm K L b` is `spectralValue (minpoly K b)` by definition — and `evalNorm`
  at `⊥` is `spectralValue (minpoly K (mk ⊥ b))`: `minpoly.algHom_eq` along `L ⧸ ⊥ ≃ L`; [U] none. SURVIVED.
- **L3.10** fibre upper bound (T016) — Q: `bgr-3.8.md:85–90` (b) and p. 172 "the spectral norm on `(B/y)[X]/(q_ν)` over
  `B/y` (which equals the spectral norm over `k` by Proposition 3.2.2/4)". D: `norm_root_le_spectralValue`,
  `spectralNorm.eq_of_tower`, `spectralNorm.normedField`, `spectralNorm.normedAlgebra'` (verified; the last needs
  `[CompleteSpace K]` — section repaired). A: [D] `norm_root_le_spectralValue` takes `p : K[X]` over the BASE field and
  `f : AlgebraNorm K L`: we apply it with base `L := B/y` and extension the residue field `E` — needs `NormedField L`
  (`spectralNorm.normedField K L`, complete `K`) and `f := spectralAlgNorm L E` — both exist; [H] `IsPowMul f` and
  `IsNonarchimedean f` for `spectralAlgNorm L E` hold with `L` ultrametric (`IsUltrametricDist L` from
  `isNonarchimedean_spectralNorm`); [E] `x` arbitrary: `E` is a field (maximal ideal), fine. SURVIVED.
- **L3.11** THE FIBRE COMPUTATION (T017) — Q: `bgr-3.8-proofs.md` p. 172 "`|f̄_y|_sup = max_ν |f̄_ν|_ν = max_ν σ(q_ν) =
  σ(q_y)`" and 1.5.4 "`σ(p)` … the norm of its largest root". D: `max_norm_root_eq_spectralValue` (verified: `(⨆ x, if x ∈ s
  then f x else 0) = spectralValue p` for `mapAlg K L p = ∏ (X − C a)`), `SplittingField.splits`, `Splits.eq_prod_roots_of_monic`,
  `AdjoinRoot.liftAlgHom` (verified name), Layer 0 `isMaximal_ker_of_isAlgebraic`, `evalNorm_eq_norm_algHom`. A: [C]
  BGR factor `q_y = ∏ q_ν^{n_ν}` and use the reduced ring; we use the splitting field and the kernel of evaluation at a
  maximal root — is the kernel a maximal ideal of `AdjoinRoot q`? Yes: `ev : AdjoinRoot q → E` lands in a field algebraic
  over `K`, so `ker` is maximal (Layer 0 lemma) — the point is the factor containing `a₀`; [E] `natDegree q = 0`: no roots —
  excluded by `0 < natDegree`; [D] `max_norm_root_eq_spectralValue` needs `DecidableEq E` and `f 1 = 1`
  (`spectralAlgNorm_one`) — available; [U] the `AlgebraNorm L E` must be `K`-spectral: `spectralNorm.eq_of_tower` identifies
  `spectralNorm L E = spectralNorm K E` on `E` — so `evalNorm` (a `K`-spectral value) equals `‖a₀‖` for the `L`-norm.
  SURVIVED.
- **L3.12** `supSpectralValue_minpoly_le_supSeminorm` (T018) — Q: `bgr-3.8-proofs.md` Ad (a) in full (quoted in T018).
  D: `minpoly.ker_eval` (verified: needs `IsIntegrallyClosed R`, `IsDomain S`, `Module.IsTorsionFree R S`),
  `AdjoinRoot.quotEquivQuotMap` (verified), L3.6–L3.11, L1.29–L1.33. A: [H] `minpoly.ker_eval` needs `IsDomain A` — hence
  D8; [C] reduction to `B[f]`: `A` integral over `B[f]`? `A` integral over `B` ⇒ over the intermediate `B[f]`
  (`Algebra.IsIntegral.tower_top`) and `B[f] → A` injective — so L3.6 applies; [C] the quotient `AdjoinRoot q ⧸ yA` equals
  `AdjoinRoot q̄` over the FIELD `B ⧸ y` — `quotEquivQuotMap` gives `(B ⧸ y)[X] ⧸ (q̄)` = `AdjoinRoot q̄` definitionally;
  [E] `q̄` has positive degree (monic, degree preserved) — needed for L3.11, holds. SURVIVED.
- **L3.13** M1 (T019) — Q: 3.8.1/7 (a). D: L2.13 + L3.12. A: [C] both halves are for the same `q = minpoly B f` — yes;
  [E] `f = 0`: `minpoly = X`, `σ = 0 = |0|_sup` — consistent. SURVIVED.
- **L3.14–L3.15** scaled minimal polynomial, (d) (T020) — Q: `bgr-3.8-proofs.md` Ad (d) (quoted in T020). D: `scaleRoots`
  API (verified), `minpoly.isIntegrallyClosed_dvd`, `eq_of_monic_of_dvd_of_natDegree_le`. A: [E] `b = 0` excluded for the
  minpoly lemma (`hb`), handled separately in (d); [H] the degree equality `deg(bf) = deg f` uses `b` invertible in
  `Q(B)` — true for `b ≠ 0` in a domain; [S] BGR assume multiplicativity on `B` for (d) "if" — our `hB`. SURVIVED.
- **L3.16–L3.17** (b), (c) (T021) — Q: Ad (b), Ad (c) (quoted in T021). D: L2.11, L3.11, L3.1, M1. A: [E] `|f|_sup = 0` in
  (b): any point (domain ⇒ nontrivial ⇒ a point exists) — handled; [C] transporting the attained point from
  `AdjoinRoot q̄` to `A`: through `B[f] ⧸ y B[f] ≅ AdjoinRoot q̄` (L3.12's equivalences) and going up `B[f] → A` (L3.1
  needs `A` integral over `B[f]`, injective — yes); [H] (c) needs `A` reduced: a domain is reduced — fine. SURVIVED.
- **L3.18** 3.8.1/8 uniform (T022) — Q: `bgr-3.8-proofs.md` 3.8.1/8 proof (quoted in T022). D: L2.11, M1, `Nat.dvd_factorial`.
  A: [S] BGR's statement is non-uniform (`m` depends on `f`) with `|k_a|`; ours assumes `|B|_sup ⊆ ‖K‖` and a degree
  bound — a different (stronger-hypothesis, stronger-conclusion) statement, recorded as D6, used only for `T_d`; [E]
  `|f|_sup = 0`: `0^{n!} = 0 = ‖0‖` — fine; [C] `j ∣ n!` for `1 ≤ j ≤ n` — yes. SURVIVED.

**Internal node (3.8.1/7 ⇒ 6.2.1/4 (i),(ii) for domains).** [C] Needs `T_d` integrally closed (Layer 0 instance), MMP on
`T_d` (Layer 0 `exists_evalNorm_eq_norm`), `|·|_sup = ‖·‖` on `T_d` (Layer 0): all present. SURVIVED.

## G4. `SupSeminorm/Banach.lean` — BGR 3.8.2/3–6 (T023–T027)

**Source and prose proof.** `bgr-3.8-proofs.md`: 3.8.2/3 via closed graph through `Max_k A` and 3.8.1/9; 3.8.2/4 as its
corollary; 3.8.2/5 "`|f|_sup ≤ |f|_r` … `|f|_r ≤ max |φ(b_i)|_r^{1/i} ≤ max |φ(b_i)|^{1/i}` … `|f|_r ≤ C |f|_sup` … both
power-multiplicative"; 3.8.2/6 via induction `f^j ∈ Σ R f^i`.

**Leaves.**
- **L4.1–L4.3** (T023) — Q: 3.8.2/3 proof "Provide `A/x` and `B/φ⁻¹(x)` with the spectral norm. The map `φ̄` is then an
  isometry … by Lemma 3.8.1/9, we may finish the proof by using the Closed Graph Theorem"; 3.8.2/4. D: Layer 1
  `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional` (signature read: `𝔅`, closed, comap closed, finite-dim,
  `sInf 𝔅 = ⊥`), `Ideal.IsMaximal.isClosed` (verified: `NormedRing` + `HasSummableGeomSeries`), L1.24–L1.26,
  `LinearEquiv.continuous_symm`. A: [H] Layer 1's lemma needs `FiniteDimensional K (B ⧸ 𝔟)` — BGR only have algebraic
  residue fields; we add `hfin` (affinoid algebras satisfy it) — recorded in T023's generality; [D] `HasSummableGeomSeries A`
  from completeness — instance exists for complete normed rings (`NormedRing.instHasSummableGeomSeries`?—check at ticket
  time; else `Ideal.IsMaximal.isClosed`'s own instance path); [E] `A` trivial: `Continuous φ` into a subsingleton is
  automatic. SURVIVED.
- **L4.4–L4.6** (T024) — Q: 3.8.2/5 "From Corollary 2 one deduces immediately that `|f|_sup ≤ |f|_r`"; 6.2.3 intro. D:
  `smoothingFun` (abbrev, verified), `le_ciInf`, PFA `IsPowerBounded.exists_norm_pow_le`. A: [E] `i : ℕ+` avoids `n = 0`;
  [D] `smoothingFun μ x = ⨅ n : ℕ+, μ (x ^ n) ^ (1 / (n : ℝ))` — unfolds by `rfl`; [H] `IsPowerBounded.exists_norm_pow_le`
  needs `NontriviallyNormedField K` + `NormedAlgebra K A` — in scope. SURVIVED.
- **L4.7** (T025) — Q: 3.8.2/5 "one can apply Proposition 3.1.2/1 to `A/ker | |_r`". D: `smoothingSeminorm`,
  `isPowMul_smoothingFun`, `isNonarchimedean_smoothingFun`, `smoothingFun_le_self` (names read from the Mathlib file).
  A: [D] `isNonarchimedean_smoothingFun` needs `IsNonarchimedean μ` — the norm of an ultrametric ring is
  (`IsUltrametricDist.isNonarchimedean_norm`); [E] `natDegree q = 0`: `iSup` over `Fin 0` is `0` and `A` is trivial — fine;
  [C] the `RingSeminorm` `smoothingSeminorm` is submultiplicative by construction — yes. SURVIVED.
- **L4.8** 3.8.2/5 (T026) — Q: verbatim in T026. D: L4.4, L4.7, M1, the contraction argument (BGR 1.3.1/2). A: [H] BGR's
  "`φ` continuous for `|·|_sup`" = `‖algebraMap b‖ ≤ C |b|_sup` — our `hC`; [E] `|f|_sup = 0` ⇒ `μ'(f) = 0`: from
  `μ'(f)^m ≤ C' · 0` — fine; [C] `C^(1/j) ≤ max 1 C` for `j ≥ 1` — yes. SURVIVED.
- **L4.9–L4.10** 3.8.2/6 (T027) — Q: verbatim in T027. D: PFA `isPowerBounded_of_norm_pow_le`,
  `IsTopologicallyNilpotent.of_norm_lt_one`, L4.8. A: [E] the induction's base `j < n`: `f^j` itself with `c = e_j` — fine;
  [H] "`R` bounded" needs continuity of `B → A` — `hC`; [C] (a)⇔(b) uses `IsTopologicallyNilpotent` of `f^m` ⇒ of `f`
  — BGR 1.2.5/7's division argument, stated in the sketch. SURVIVED.

## G5. `BanachAlgebra/Module.lean` — BGR 3.7.2/2, 3.7.3/1 (T028–T030)

**Source and prose proof.** `bgr-3.7.md:39–56`: 3.7.2/1–2 (finitely generated submodules of complete modules over a
complete ring are closed; Nakayama for `Ǎ`, 1.2.4/6) and 3.7.3/1 ("Every submodule `M′` of a module `M ∈ 𝔐_A` is closed").
Layer 1 proved the ideal case; the module case is the same proof with `•`.

**Leaves.**
- **L5.1–L5.2** (T028) — Q: `bgr-3.7.md:142` 1.2.4/6 "Let `A` be complete and let `M` be an `A`-module. Let `N` be a
  submodule of `M` such that …" and 3.7.2/1. D: `Submodule.le_of_le_smul_of_le_jacobson_bot` (Mathlib Nakayama),
  `ContinuousLinearMap.exists_preimage_norm_le` (verified in Layer 1), PFA `openUnitBallIdeal_le_jacobson_bot`. A: [H]
  `K` dropped silently? — REPAIRED by `include K`; [D] Nakayama needs `M` finitely generated over `Å` — the span of
  finitely many `x i`; [E] `m = 0`: vacuous. SURVIVED.
- **L5.3** (T029) — Q: 3.7.2/2 (`bgr-3.7.md:39`). D: L5.1–L5.2, `Submodule.topologicalClosure`, noetherianity of `Aⁿ`
  (`isNoetherian_pi`). A: [C] the closure of `N` is finitely generated — `Fin n → A` is a noetherian module over a
  noetherian ring (`isNoetherian_pi`); [E] `N = ⊥` or `⊤`: trivially closed, the argument still applies; [H] the
  generators of `N̄` approximated from `N` with `C`-controlled coefficients — the open-mapping lemma is applied to the
  CLOSED `N̄` (hypothesis `hN`) — consistent. SURVIVED.
- **L5.4–L5.5** (T030) — Q: 3.7.3/1 and BGR p. 242 "Viewing `A` as a submodule of the finite `A`-module `A'`, we see by
  Proposition 3.7.3/1 that `A` is closed in `A'`". D: `ContinuousLinearMap.isOpenMap`, `IsOpenMap.isQuotientMap`,
  `Fintype.linearCombination`. A: [H] the quotient-map argument needs `π` surjective and continuous — both hypotheses;
  [D] `ContinuousSMul A M` is needed for continuity of `a ↦ a • x i` — hypothesis; [U] `M` must be a Banach `K`-space
  (`NormedSpace K M`, `CompleteSpace M`) for the open mapping theorem — in the variables. SURVIVED.

## G6. `SupSeminorm/FunctionAlgebra.lean` — BGR 3.8.3/1–5, 3.8.3/7 (T031–T037)

**Source and prose proof.** `bgr-3.8-proofs.md` 3.8.3: Def 1, Lemma 2 (equivalence of norms), Lemma 3 (uniqueness,
via 1.3.1/3), Lemma 4 (closed subalgebras), Cor 5 (finite monomorphisms, via 3.7.2/2), Thm 7 (proof: `Q(A)` finite over
`Q(B)`, weakly cartesian by weak stability; `A ⊂ A' = Σ B a_i/b`; `A'` complete finite `B`-module for `|·|_sp`; `A` closed
in `A'` by 3.7.2/2; `|f|_sup = |f|_sp` by 3.8.1/7 (a)). Our route (plan §5.5): coordinates `θ : A → Bⁿ`, closed range
(3.7.2/2), closed graph for continuity, open mapping for `‖f‖ ≤ C‖θ f‖`, weak stability for `‖θ f‖ ≤ C|f|_sp = C|f|_sup`.

**Leaves.**
- **L6.1–L6.2** (T031) — Q: 3.8.3/1–3 and 1.3.1/3 "Let `| |, | |'` be pm-semi-norms on `A` such that there are real
  numbers `ρ, ρ' > 0` with `| |' ≤ ρ| | ≤ ρ'| |'`. Then these semi-norms are equal". D: L1.15–L1.23, Layer 0
  `supSeminorm_le_norm`. A: [E] `f = 0`; [H] `IsPowMul ‖·‖` is a hypothesis (true for the Gauss norm, false in general) —
  stated as such; [S] D3: "complete norm" ↔ "equivalent to the given complete norm" — BGR 3.8.3/2 exactly. SURVIVED.
- **L6.3–L6.4** (T032) — Q: 3.8.3/4 proof and 3.8.3/5 proof (quoted in T032). D: open mapping, L1.28, L5.4–L5.5. A: [H]
  BGR 3.8.3/4 has no norm on `B` (it is transported); with a given Banach norm on `B` the extra `hφ : Continuous φ`
  is needed — included; [C] in 3.8.3/5, `A` as a normed `B`-module needs `ContinuousSMul B A` ⇐ `φ` continuous
  (BGR: "By Proposition 3.8.2/3, the map `φ` is continuous") — we take `hφ` as hypothesis (6.2.1/5 supplies it for
  reduced affinoid targets); [E] `B` trivial: fine. SURVIVED.
- **L6.5–L6.6** (T033) — Q: p. 181 "there is a universal denominator `b ∈ B − {0}` such that `A ⊂ A' := Σ B a_i/b ⊂
  Q(A)`"; 3.8.1/7 preliminaries. D: Layer 1 `FractionRing.finiteDimensional_of_finite` (signature read),
  `IsLocalization.exist_integer_multiples` (verified), `exists_linearIndependent`/`Basis.ofVectorSpace`. A: [E] `A = B`
  (`n = 1`, `a = 1`, `b = 1`) — fine; [C] linear independence over `B` of elements of `A` coming from a `Q(B)`-basis:
  a `B`-relation is a `Q(B)`-relation (`algebraMap` injective) — yes; [H] "`A` finite over `B`" is used for the
  universal denominator (finitely many generators) — hypothesis `Module.Finite B A`. SURVIVED.
- **L6.7–L6.8** (T034) — Q: p. 182 "By Proposition 3.7.2/2, the `B`-submodule `A` of `A'` is closed … `A` is complete
  and hence a `k`-Banach algebra"; 3.8.2/3 (closed graph). D: L5.3, `LinearMap.continuous_of_isClosed_graph` (verified
  name), `ContinuousLinearMap.exists_preimage_norm_le`. A: [H] `K` must be in the statement (open mapping) — REPAIRED
  (`include K`); [C] closed graph: the limit identity `b • f = ∑ v i • a i` uses continuity of `algebraMap B A` — `hcont`;
  [D] `θ` is `B`-linear; `K`-linearity for the closed graph theorem: `restrictScalars K` via `IsScalarTower K B A` — in
  the variables; [E] `n = 0`: then `b • f = 0` for all `f`, so `A` is trivial (torsion-free, `b ≠ 0`): all claims hold.
  SURVIVED.
- **L6.9** (T035) — Q: p. 182 "From Proposition 3.8.1/7 (a), we derive `|f|_sup = |f|_sp` for all `f ∈ A`" and the Remark
  after 3.8.1/9. D: `minpoly.isIntegrallyClosed_eq_field_fractions'` (verified), Layer 0 `IsFractionRing.normedField`,
  `normAbsoluteValue_algebraMap`, M1. A: [D] `isIntegrallyClosed_eq_field_fractions'` needs `IsDomain S` with `S :=
  FractionRing A` and `[Algebra K S] [IsScalarTower R K S]` — the hypotheses `[Algebra (FractionRing B) (FractionRing A)]
  [IsScalarTower B …]` provide exactly this; [H] `NormMulClass B` for the fraction-field norm — in the variables; [C]
  `spectralValue` over `Q(B)` of the mapped polynomial vs `supSpectralValue K` over `B`: termwise equal via
  `normAbsoluteValue_algebraMap` and `hBsup` — yes. SURVIVED.
- **L6.10** (T036) — Q: p. 181 "Since `Q(B)` is weakly stable, all these extensions are weakly `Q(B)`-cartesian under their
  spectral norm" + Layer 0's definition of `IsWeaklyStable` (coordinate functionals bounded by the spectral norm). D:
  Layer 0 `IsWeaklyStable` (definition read), `Module.Basis.extend`, L6.9. A: [U] universes: `IsWeaklyStable (FractionRing B)`
  quantifies over `L : Type u`; `FractionRing A : Type u` iff `A : Type u` — REPAIRED (D12); [H] `Q(A)` is a field
  (`A` domain) — D1; [C] the coordinate functionals are for a basis extending `a` — `θ f` are the first `n` coordinates of
  `algebraMap (b • f)`; [E] `|f|_sup = 0` ⇒ `f = 0` (domain, M1 + T021 (c)) ⇒ `θ f = 0` — consistent. SURVIVED.
- **L6.11** 3.8.3/7 domain (T037) — Q: Theorem 7 statement. D: L6.5–L6.10. A: [C] constants multiply: `‖f‖ ≤ C₁‖θ f‖ ≤
  C₁C₂|f|_sup` — yes; [H] `HasSupSeminorm K A` derived from `B` (L3.4) — yes; [S] D1 recorded. SURVIVED.

## G7. `Affinoid/SupSeminorm.lean` — BGR 6.2.1/1, 6.2.1/4–5, 6.2.2/1–2, 6.2.2/4 (T038–T046, M2 = T042)

**Source and prose proof.** `bgr-6.2-6.3.1.md` §6.2.1–6.2.2 (quoted per leaf). [Bo] 1.4/13–15 as secondary source.

**Leaves.**
- **L7.1–L7.3** (T038) — Q: p. 236 "all maximal ideals in a `k`-affinoid algebra `A` are `k`-algebraic … `|f|_sup ≤ |f|_α for
  all … epimorphisms `α: Tₙ → A`". D: Layer 1 `finiteDimensional_quotient_of_isMaximal`, Layer 0 `evalNorm_le_norm`, L1.26.
  A: [C] bounding `evalNorm K x f` through a preimage `g` needs the point `comap α x` of `Tₙ` to be maximal — L1.26 with
  algebraicity of `A ⧸ x` (first field) — no circularity (the class is being built, but L1.26 only needs the local
  instance); [E] `A` trivial: no points; [H] `IsAffinoidAlgebra` gives `n, α` — yes. SURVIVED.
- **L7.4** (T039) — Q: 6.2.2/1. D: L3.6. A: [H] integral (not finite) — L3.6 is for integral; [D] `RingHom.IsIntegral` ↔
  `Algebra.IsIntegral` under `toAlgebra` — yes. SURVIVED.
- **L7.5–L7.6** (T040) — Q: 6.2.2/2 (quoted in T040). D: M1, L3.14–L3.15, Layer 0 `IsIntegrallyClosed (TateAlgebra K n)`
  (file `Rueckert.lean` line 68), `NormMulClass` (GaussNorm.lean line 251), `supSeminorm_eq_norm`. A: [H] D8 (`A` domain);
  [D] torsion-freeness from domain + faithful — proved inline (T033's lemma is for finite `A`); [S] BGR "faithful
  `T_d`-algebra norm" = our `_mul` statement with `‖t‖`. SURVIVED.
- **L7.7–L7.8** MMP (T041, T042) — Q: 6.2.1/4 proof (both paragraphs quoted). D: Layer 1 `exists_finite_injective`, L3.16,
  Layer 0 `exists_evalNorm_eq_norm`, L1.34, L1.29. A: [E] `A` trivial for M2 — `[Nontrivial A]`; [C] lifting a point from
  `A ⧸ 𝔭` to `A`: `comapPoint (mkₐ)` with `evalNorm_comapPoint` — yes; [H] `A ⧸ 𝔭` is a domain for a minimal prime —
  `Ideal.minimalPrimes.isPrime`-type (`minimalPrimes` ⊆ `IsPrime`) — yes; [S] matches BGR's two-step proof. SURVIVED.
- **L7.9–L7.11** value group (T043) — Q: 6.2.1/4 (ii) and proof; 3.8.1/8; [RM] §2.2.2. D: L3.18, Layer 1
  `FractionRing.finiteDimensional_of_finite`, `minpoly.natDegree_le` (verified, needs `Module.Free` — over a field,
  automatic), Layer 0 coefficient norms. A: [E] `|f|_sup = 0` excluded by hypothesis; trivial `A` — `m := 1`, vacuous;
  [C] uniformity across minimal primes: `m := ∏ m_𝔭` — the `|f|_sup = |mk f|_sup` identity (L1.34) is needed, yes;
  [D] `minpoly.natDegree_le` is over the fraction FIELD; the degree over `T_d` equals it via
  `isIntegrallyClosed_eq_field_fractions'` — yes. SURVIVED.
- **L7.12–L7.14** (iii) (T044) — Q: 6.2.1/4 (iii) and the Remark "assertion (iii) … is equivalent to the fact that each
  `Tₙ` is a Jacobson ring". D: L1.25, Layer 1 `isJacobsonRing`, `IsJacobsonRing.out` (verified). A: [S] BGR prove (iii)
  through minimal primes; the Jacobson route is BGR's own Remark — recorded; [E] trivial ring: `0 = 0`, nilpotent — fine;
  [C] `jacobson ⊥ = radical ⊥`: from `IsJacobsonRing.out` on the radical ideal `radical ⊥` plus monotonicity — yes.
  SURVIVED.
- **L7.15** 6.2.1/5 (T045) — Q: "If `A` is a reduced `k`-affinoid algebra, then each homomorphism of a (not necessarily
  Noetherian) `k`-Banach algebra into `A` is continuous." D: L4.1–L4.2, L7.13. A: [H] `hfin` from Layer 1; [E] none.
  SURVIVED.
- **L7.16–L7.17** 6.2.2/4 (T046) — Q: proof quoted in T046. D: Layer 1 `exists_finite_injective_comp` (finite φ — D10),
  M1, L2.13–L2.17, L1.34, `Ideal.sInf_minimalPrimes` (verified). A: [H] BGR's `ψ` for INTEGRAL `φ` — D10 (finite);
  [C] `q*(f) ∈ ⋂ 𝔭_i = nilradical`: `sInf (minimalPrimes A) = radical ⊥` — verified name; [E] `A` trivial excluded
  (`[Nontrivial A]`); `e = 0` impossible unless `q*(f)^0 = 1 = 0`. SURVIVED.

## G8. `Affinoid/PowerBounded.lean` — BGR 6.2.3/1–3, §2.3.5 (T047–T052, M3 = T050)

**Leaves.**
- **L8.1–L8.4** (T047) — Q: 6.2.3/4 "`Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}`", 1.2.5/2, 1.2.5/7. D: L1.15–L1.23.
  A: [E] `smul_mem'` with `|c|_sup` possibly `> 1`? `c ∈ Å` has `|c| ≤ 1` — fine; [C] radicality uses `supSeminorm_pow`
  with `n ≠ 0` — `n = 0` gives `1 ∈ Ǎ`, impossible unless trivial ring, where everything is in `Ǎ` anyway (then
  `Ǎ = ⊤` is radical) — fine. SURVIVED.
- **L8.5–L8.6** 6.2.3/1 (T048) — Q: proof quoted in T048. D: L4.6, L7.16–L7.17 (finite presentation), Layer 1
  `continuous_presentation`, PFA `isPowerBounded_of_norm_pow_le`. A: [H] BGR's `φ(T̊_d)` bounded = continuity of the
  presentation — Layer 1; [C] induction keeps the coefficients in `T̊_d`: needs `|t_i| ≤ 1` AND the ultrametric inequality
  for sums — Gauss norm is ultrametric; [E] `n = 0`: `q = 1`, impossible in a nontrivial ring; trivial ring: everything
  is power-bounded and `|f|_sup = 0 ≤ 1`. SURVIVED.
- **L8.7–L8.9** 6.2.3/2 (T049) — Q: proof quoted in T049. D: L7.9–L7.11, L8.5, M2. A: [E] `|f|_sup = 0`: nilpotent, hence
  topologically nilpotent — handled; [C] `c • f^m` power-bounded ⇒ `f^m` topologically nilpotent since `‖c‖ > 1`:
  `‖(f^m)^k‖ = ‖c‖^{-k} ‖(c f^m)^k‖ ≤ M ‖c‖^{-k} → 0` — yes; [H] (ii)⇔(iii) needs `Nontrivial A` for the attained sup —
  included. SURVIVED.
- **L8.10** M3 (T050) — Q: 6.2.3/3 proof (quoted). D: L4.5, L7.9–L7.11, L8.5, `smoothingFun_apply_of_map_mul_eq_mul`
  (name read from the Mathlib file). A: [C] scaling: `μ'(c • g) = ‖c‖ μ'(g)` needs `algebraMap c` norm-multiplicative
  (`‖c • x‖ = ‖c‖‖x‖` in a `NormedAlgebra`: `norm_smul`) — yes; [E] `|f|_sup = 0` handled by nilpotency; [H] BGR assume
  `|f|_sup = 1` after scaling by `c, m` — same. SURVIVED.
- **L8.11–L8.14** (T051) — Q: [RM] §2.4.3; BGR 1.2.5/2. D: Lipschitz API, `AddSubgroup.isOpen_of_mem_nhds`. A: [E] `A`
  trivial: all sets trivially open/closed; [H] `|·|_sup ≤ ‖·‖` is Layer 0 for Banach `A` — in scope. SURVIVED.
- **L8.15–L8.16** (T052) — Q: 3.8.3/6 end of proof (quoted in T052); [RM] §2.3.5. D: PFA `IsBounded.exists_norm_le_of_normedAlgebra`,
  `exists_mem_Ioc_zpow`. A: [E] `|f|_sup = 0` with `f ≠ 0` (nilpotent): `c^{-m} • f ∈ Å` for all `m`, bounded ⇒ `f = 0`
  — the iff still holds (the `∃ C` side also forces `f = 0`); [H] `NontriviallyNormedField K` for `‖c‖ > 1` — yes;
  [C] both directions as stated. SURVIVED.

## G9. `Affinoid/Reduction.lean` — BGR 6.2.3/4–5 (T053–T055)

**Leaves.**
- **L9.1–L9.4** (T053) — Q: 6.2.3/4; 1.2.5/6–7; [RM] §2.3.4. D: PFA `maximalIdeal_unitClosedBall`, `Ideal.Quotient.lift`,
  L8.3. A: [E] `A` trivial: `Å = Ǎ = {0}`, `Ã` trivial, reduced — fine; [D] `IsReduced (R ⧸ I) ↔ I.IsRadical` — Mathlib
  `Ideal.isRadical_iff_quotient_reduced` (name to verify; alternative: prove directly from radicality); [U] the `K̃`-algebra
  is a `def`-based instance (`toAlgebra`), no diamond (no other `Algebra K̃ (Reduction K A)` instance exists). SURVIVED.
- **L9.5–L9.6** (T054) — Q: [RM] §2.3.4; Layer 0 `reductionEquiv`. D: Layer 0 `MvPowerSeries.Restricted.reductionEquiv`
  (signature read: `unitClosedBall ⧸ openUnitBallIdeal ≃+* MvPolynomial σ (ResidueField (unitClosedBall K))`),
  `RingEquiv.subringCongr`, `Ideal.quotientEquiv`. A: [D] the two subrings are propositionally, not definitionally, equal —
  transported through `subringCongr`, the quotient through `quotientEquiv` with the ideal-map equality — yes; [E] `n = 0`.
  SURVIVED.
- **L9.7–L9.9** 6.2.3/5 (T055) — Q: 6.2.3/5; 1.5.3/1 proof; 1.5.1 (all quoted in T055). D: L7.9–L7.11, L7.13, L9.4. A: [H]
  BGR's "valuation" includes `|f| > 0` for `f ≠ 0` (1.5.1/1 (a)) — our `hnorm`; [C] 1.5.3/1 (i) needs a multiplicative
  element `m` with `|m a^s| = 1`: scalars `c • 1` are multiplicative (`supSeminorm_smul`) — yes; [E] `isDomain_reduction`
  needs `Ǎ ≠ Å`: `|1|_sup = 1` for nontrivial `A` — `[Nontrivial A]` included; [S] the "if" direction uses `Ã` domain to
  conclude multiplicativity — matches BGR's "we conclude that". SURVIVED.

## G10. `Affinoid/FunctionAlgebra.lean` — BGR 6.2.4/1 (T056–T059, M4 = T058)

**Leaves.**
- **L10.1** domain case (T056) — Q: 6.2.4/1 proof, first paragraph (quoted in T056). D: L6.11, Layer 0
  `isWeaklyStable_fractionRing` (statement read: `letI := IsFractionRing.normedField …; IsWeaklyStable …`, `[CharZero K]`),
  Layer 1 `continuous_of_isAffinoidAlgebra'`. A: [H] `CharZero K` — D2; [U] `A : Type u` — D12; [D] the `letI` shapes of
  `hws` in T037 and Layer 0's lemma coincide — same spelling by construction. SURVIVED.
- **L10.2–L10.4** diagonal map (T057) — Q: 6.2.4/1 proof, second paragraph (quoted in T057). D: `Ideal.Quotient.normedCommRing`
  (verified: needs `IsClosed`), `Ideal.Quotient.normedAlgebra`, Layer 1 `isClosed_ideal`, L5.5, open mapping. A: [D] the
  closedness instances are `haveI` inside the statements (so the quotient norms exist) — builds; [C] `range (RingHom.pi …)`
  is an `A`-submodule of a finite `A`-module — `Module.Finite.pi` + `Module.Finite.quotient` — yes; [E] `ι` empty: the
  Pi type is a singleton, range closed, `⨅ = ⊤ = ⊥` only for trivial `A` — the bound holds with any `C`. SURVIVED.
- **L10.5** M4 (T058) — Q: 6.2.4/1 statement and "due to Lemma 6.2.1/3, the norm `| |` induces the supremum norm on `A`".
  D: L10.1–L10.4, L1.34/L1.30, `Ideal.sInf_minimalPrimes`, `nilradical_eq_zero`. A: [C] `‖π f‖ = max_i ‖mk_i f‖ ≤ max_i C_i
  |mk_i f|_sup ≤ (max C_i) |f|_sup` — uses `supSeminorm_mk_le` (L1.30), not the attained form — fine; [H] residue norms on
  `A ⧸ 𝔭_i` are complete `K`-algebra norms (ultrametric, `NormOneClass` by Layer 1 `normOneClass_of_ne_top`) so T056
  applies to each — yes; [E] `A` trivial is reduced: `ι = ∅`, any `C`. SURVIVED.
- **L10.6–L10.7** (T059) — Q: [RM] §2.3.5, §2.4.3. D: L8.15, L10.5. A: [E] none beyond the above. SURVIVED.

## G11. `Affinoid/ReductionFunctor.lean` — BGR 6.3 intro, 6.3.1/1–6 (T060–T064, M5 = T064)

**Leaves.**
- **L11.1–L11.7** functor (T060) — Q: 6.3 intro (quoted in T060). D: L1.28, `Ideal.Quotient.lift`. A: [C] `φ̊` maps `B̌` to
  `Ǎ` by the contraction — yes; [E] trivial rings — fine; [U] `reductionAlgHom` over `K̃` needs `commutes'` for residue
  classes — `Ideal.Quotient.mk_surjective`. SURVIVED.
- **L11.8–L11.10** 6.3.1/1–3 (T061) — Q: quoted in T061. D: L7.9–L7.11, L7.12–L7.14, L11.3. A: [E] `|g|_sup = 0` in
  6.3.1/1 — BGR handle it, so do we; [C] 6.3.1/2 `←`: `φ̃` injective from the isometry: `|φ b| < 1 → |b| < 1` — yes;
  `→`: contrapositive through 6.3.1/1 — yes; [H] no norm needed. SURVIVED.
- **L11.11–L11.12** 6.3.1/4 (T062) — Q: quoted in T062. D: L8.7, L8.14, L9.4, `Ideal.map_comap_of_surjective`. A: [H]
  strictness is used exactly once: `φ(B̌)` open in `range φ` — our `IsStrictMap` gives it; [C] `g^n − b ∈ ker φ̊`: both
  in `B̊` — `b ∈ B̌ ⊆ B̊` — yes; [D] `Ideal.map_radical_of_surjective` — name to verify; fallback via `comap_radical` is in
  the sketch; [E] `g ∈ B̌` already: trivial. SURVIVED.
- **L11.13–L11.14** 6.3.1/5, (i)⇒(iii) (T063) — Q: quoted in T063. D: L11.11, L8.3, L7.12. A: [C] `rad B̌ = B̌` — L8.3;
  [E] `ker φ = ⊥` is `≤ nilradical` — yes. SURVIVED.
- **L11.15–L11.16** M5 (T064) — Q: 6.3.1/6 proof (quoted in T064). D: L7.13, L10.5, Layer 0 `supSeminorm_le_norm`, Layer 1
  continuity. A: [H] `CharZero K` and `B : Type u` — D2/D12; [C] bi-Lipschitz ⇒ homeomorphism onto the image ⇒ images of
  open sets open in the image — yes (`IsStrictMap` as defined); [E] `B` trivial: `φ` is trivially strict. SURVIVED.

## G12. `Affinoid/SupExamples.lean` — [RM] Examples, BGR 6.3.1 Examples 1–2 (T065–T069)

**Leaves.**
- **L12.1–L12.4** (T065) — Q: [RM] Examples. D: Layer 0/1 facts. A: [E] `n = 0`: no `i : Fin 0`; [H] `Nontrivial Tₙ` for
  `|m|_sup = ‖m‖` — Layer 0 instance. SURVIVED.
- **L12.5–L12.9** (T066) — Q: [RM] Examples. D: Layer 1 `Affinoid/Examples.lean` (`ker_aeval_eq_span`,
  `nonempty_algEquiv_quotient_X_sub`, `isAffinoidAlgebra_quotient_X_sq_sub`, lines 35–130 read), Layer 0 Weierstrass
  division, L3.10–L3.11, L7.12, L8.16. A: [H] `‖a‖ ≤ 1` for the ideals to be proper and distinguished — included; [C]
  `(X² − a)`: the identification `T₁ ⧸ (X² − a) ≃ AdjoinRoot (X² − C a : K[X])` is a Layer 0/1 Weierstrass fact — the exact
  available statement is to be located at ticket time (`Affinoid/Examples.lean` has the `X² − p`, `‖a‖ < 1` case
  `finrank_quotient_X_sq_sub`; for `‖a‖ = 1` the same division applies) — if only `‖a‖ < 1` is available the ticket
  restricts the hypothesis (B2-free: a strengthening of a hypothesis on an example); [E] `a = 0`: `|X|_sup = 0 = ‖0‖^{1/2}`
  — `Real.zero_rpow` fine. SURVIVED (with the noted fallback).
- **L12.10–L12.13** annulus (T067) — Q: BGR 6.2.3 example (quoted in T067). D: Layer 1 `extendAlgHom`, Layer 0
  `isMaximal_ker_of_isAlgebraic`, `evalNorm_eq_norm_algHom`, `isUnit_iff_norm_coeff_lt`. A: [H] `Nontrivial (T₂ ⧸ I)`:
  `XY − c` not a unit — Layer 0 criterion (the coefficient of `XY` has norm `1 = ‖XY − c‖`); [C] the point is the kernel of
  an evaluation, not BGR's explicit ideal — same point; [E] `c = 0`: `|f₁f₂|_sup = 0 = ‖0‖` — fine. SURVIVED.
- **L12.14–L12.18** Example 2 (T068) — Q: quoted in T068. D: Prod instances (Mathlib + PFA), Layer 1 `extendAlgHom_apply`.
  A: [H] the sum formula `φ g = ∑ gₙ (c,0)ⁿ` — `extendAlgHom_apply` (Layer 1, line 121; its exact form to be read at
  ticket time); [C] `τ(1,0) ∉ range K̃` — the ultrametric argument is sound; [E] `c = 0` allowed for non-surjectivity
  (then `φ(X) = 0`). SURVIVED.
- **L12.19–L12.21** Example 1 (T069) — Q: quoted in T069; D5. D: Layer 0 spectral-norm instances, L11.9. A: [H] finite
  extension of a complete field is complete for the spectral norm — `spectralNorm.completeSpace`; [E] `L = K`: finrank
  `1`, the non-surjectivity lemma's hypothesis fails — fine. SURVIVED.

**Internal node (whole layer ⇒ chain root, T070).** [U] no `PhD.Main` import (grep at the gate); [C] every module builds now
with sorries only. SURVIVED.

## Feasibility assessment

Every leaf is discharged by a verified Mathlib name, a Layer 0/1 declaration, or a sketch mirroring the source's own
proof. The two genuinely new pieces of infrastructure are the fibre computation (T017: one splitting field plus Mathlib's
`max_norm_root_eq_spectralValue`) and the module version of closedness (T029: a port of Layer 1's ideal case). The one
place where the formalisation chooses a different route from the source is 3.8.3/7, where BGR's Dedekind decomposition
is replaced by the domain case plus the minimal-primes argument BGR themselves use for 6.2.4/1 (D1); the coordinate-map
route (T034–T036) is a transcription of BGR's "`A ⊂ A' = Σ B a_i/b`, closed by 3.7.2/2" with the comparison to the
given norm done by the closed graph theorem as in BGR 3.8.2/3. No multi-week API gap. Open risks: the exact Mathlib names
marked "verify" (alternatives given), and the `(X² − a)` example's Weierstrass identification for `‖a‖ = 1` (fallback
recorded).
