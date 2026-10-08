# Decomposition: p-adic functional analysis, Layer 0

Companion to `plan.md`. Every leaf below is a declaration in the skeleton, stated with `sorry`;
the pointer is `File.lean · declaration name` (names are stable, line numbers are not). Sources:
[RM] = the roadmap clause the leaf discharges, quoted verbatim; [JN] / [Bel] / [Buz07] / [Sch] /
[Wed] / [Col10] = literature, quoted verbatim with a locator `file.txt:line` into
`references/`; [SRC] = the read-only reference development `PhD/Main/…` at `747bb77`, cited by
`File.decl` for the *proof idea* only (never imported). Discharge lines name the Mathlib lemmas a
worker will call — every name was checked by elaboration (`scratch/names.lean`, `names2.lean`;
the misses are recorded where they occur). Attack categories: [1] counterexample search, [2] edge
cases, [3] hypothesis strength, [4] source drift, [5] discharge.

## Skeleton location

`PhD/TauCeti/Code/PadicFunctionalAnalysis/{Sums, UnitBall, PowerBounded, Multiplicative, Module,
Tate, NormComparison, Rescale, Residue, GaugeNorm, Huber, Examples}.lean` — 12 files, 212
declarations, 191 `sorry`s (the rest are definitions and `rfl` lemmas complete in the skeleton).

Build status: recorded in the "Gate" section at the end of this file.

## Prior-B2 consultation (Step 4.6), once for the whole tree

`b2_log.jsonl` has 8 entries (2 Newton-polygon, 6 LWX). **No leaf matches by name.** One matches by
*shape of defect*: entry 2, `LWX.exists_binomial_basis` (2026-09-03) — *"False as stated, two
independent defects … the planner's generality claim … field not char 0 … ρ > 1"*: a statement
generalised beyond its source's hypotheses. This tree generalises beyond its sources in six places,
and each is attacked explicitly rather than assumed:

| Generalisation | Where | How it was checked |
|---|---|---|
| strict bound with **no** nullity hypothesis | L1.4 | proved in full in `scratch/spot.lean` (compiles) |
| [JN] 2.1.7 for a continuous ring **homomorphism**, `‖e ϖ‖ < 1` dropped | L7.3–L7.4 | proof re-derived line by line below; both dropped hypotheses shown derivable/unused |
| [JN] 2.1.6 without the second pseudo-uniformiser `π` | L7.1–L7.2 | [JN]'s proof never uses `π`; [SRC] carries a `nolint unusedArguments` for it |
| power-boundedness criteria without `NormOneClass` | L3.2, L3.4 | `‖1‖` is a finite constant; under `NormMulClass` + `NeBot` it is forced to be `1` |
| module-valued / noncommutative unit-ball API | L2.*, L9.1 | commutativity used only where an ideal quotient or `IsAdic` appears |
| rescaled norm over a ring, not a field | L8.* | found **not** to be an `R`-module in general (erratum E3); statement restricted |

The remaining entries (theta-equivariance, segment-decorated polygons) have no counterpart here.

---

## §0.1 Sums in ultrametric groups (`Sums.lean`)

### Plain-English proof substrate

[Sch] `schneider.txt:625`: *"It follows from the strict triangle inequality that a series `∑ aₙ`
in `K` converges if and only if `(aₙ)ₙ` is a zero sequence; moreover, in this case one has
`∑ aₙ = ∑ a_{σ(n)}` for any permutation `σ` of `ℕ`."* [Bel] `bellaiche.txt` footnote 1, p. 56:
*"When the sequence `(mᵢ)ᵢ∈I` converges to `0`, it is easy to see that the sequence
`(∑_{i∈J} mᵢ)_{J∈F(I)} … converges to some limit in `M`."* Both halves are Mathlib. Everything new
is a consequence of one observation: a null family attains its largest norm, because for any index
`i₂` with `f i₂ ≠ 0` the set `{i | ‖f i₂‖ ≤ ‖f i‖}` is finite. Then the bound `‖∑' f‖ ≤ ⨆ ‖f i‖`
becomes `‖∑' f‖ ≤ ‖f i₀‖`, which gives the strict bound at once; the unique dominant term is the
strict bound applied to the family with `i₀` removed, plus the isosceles principle
(`‖x + y‖ = max` when `‖x‖ ≠ ‖y‖`). On a product, nullity of `f : ι × κ → E` is equivalent to: every
row is null and the row suprema are null — the finite exceptional set projects to a finite set of
rows. Iterated sums are then Mathlib's `tsum_prod'`, and a bounded biadditive `b` commutes with
sums one variable at a time because `b x` and `b · y` are continuous additive maps.

### Leaves

- **L1.1** `Filter.Tendsto.bddAbove_range_norm` — [RM] §0.1.1 *"such a family has bounded norms
  (`BddAbove (Set.range (‖f ·‖))`)"*. Match: literal. Discharge: `hf.norm` (then `norm_zero`) and
  `Filter.Tendsto.bddAbove_range_of_cofinite` — **proved in `scratch/names2.lean`** (2 lines).
  Attacks: [2] `ι` empty: range empty, bounded ✓. [3] needs only `SeminormedAddCommGroup`; no
  ultrametric — stated that way. [5] both lemmas verified. SURVIVED.
- **L1.2** `Filter.Tendsto.exists_forall_norm_le` — [RM] §0.1.2 *"the supremum is attained when
  some `f i ≠ 0`"*. Lean: `[Nonempty ι] … ∃ i₀, ∀ i, ‖f i‖ ≤ ‖f i₀‖`. Match: **stronger than the
  roadmap** — attained whenever `ι` is nonempty (if every `f i = 0` any index works). Discharge:
  pick `i₁`; if it is not maximal take `i₂` with `‖f i₁‖ < ‖f i₂‖`; `{i | ‖f i₂‖ ≤ ‖f i‖}` is finite
  by `hf.norm.eventually (gt_mem_nhds _)` + `Filter.eventually_cofinite`; `Finset.exists_max_image`.
  Attacks: [1] none found. [2] `f ≡ 0` on infinite `ι` ✓ (any `i₀`); singleton ✓. [3] `Nonempty` is
  necessary (no `i₀` otherwise); "some `f i ≠ 0`" is not. [5] this argument is the inner block of
  the compiled `spot.lean`. SURVIVED.
- **L1.3** `Filter.Tendsto.exists_norm_eq_iSup` — same clause, in the `⨆` form that Mathlib's
  bound uses. Discharge: L1.2 + `le_ciSup` (L1.1) + `ciSup_le`. Attacks: [2] `ι` empty excluded by
  `Nonempty` ✓ (`⨆` over `∅` is `0`, not attained). [3] as L1.2. [5] three lemmas. SURVIVED.
- **L1.4** `IsUltrametricDist.norm_tsum_lt_of_forall_lt` — [RM] §0.1.3 *"If `‖f i‖ < B` for every `i`
  and `f → 0` cofinitely, then `‖∑' f‖ < B`"*. Lean: `(hB : 0 < B) (hlt : ∀ i, ‖f i‖ < B)`, **no
  nullity hypothesis**. Match: strictly stronger — if `f` is not summable the sum is `0`; if it is,
  it is null (`Summable.tendsto_cofinite_zero`). [SRC] `05_Sharpness.norm_tsum_lt_of_forall_lt`
  carries the hypothesis. Discharge: **proved in full, `scratch/spot.lean`** (L1.2's argument +
  `IsUltrametricDist.norm_tsum_le`). Attacks: [2] `ι` empty: `‖0‖ = 0 < B` — this is why `hB` stays
  ([3]: with `ι = ∅`, `B ≤ 0` the statement fails, so `hB` is necessary; for nonempty `ι` it follows
  from `hlt`). [4] drift is in the safe direction. [5] compiled. SURVIVED.
- **L1.5** `IsUltrametricDist.nnnorm_tsum_lt_of_forall_lt` — [RM] §0.1.2 *"State the `nnnorm` form
  as well"*. Discharge: `NNReal.coe_lt_coe`, `coe_nnnorm`, L1.4. Attacks: [2] `B : ℝ≥0`, `hB`
  needed as in L1.4. [3] none to drop. [5] trivial transfer. SURVIVED.
- **L1.6** `IsUltrametricDist.norm_tsum_eq_of_forall_lt` — [RM] §0.1.3 *"if `‖f i₀‖ > ‖f i‖` for every
  `i ≠ i₀`, then `‖∑' f‖ = ‖f i₀‖`. The second is the engine of every 'leading term' argument"*.
  Lean: `(hf : Summable f)`. Match: `Summable` replaces "null + complete" — equivalent in a complete
  group, and **necessary**: [3] in an incomplete group a null non-summable family has `∑' = 0 ≠
  ‖f i₀‖`. Discharge: `hf.tsum_eq_add_tsum_ite i₀` (needs `T2`, hence `NormedAddCommGroup`); the
  tail has norm `< ‖f i₀‖` by L1.4 when `0 < ‖f i₀‖`, and is `0` when `‖f i₀‖ = 0` (then `hlt` forces
  `ι = {i₀}`); `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`. [SRC]
  `05_Sharpness.norm_tsum_eq_of_forall_lt`. Attacks: [2] `ι = {i₀}` ✓; `‖f i₀‖ = 0` ✓ (above). [4]
  the roadmap's `>` and the Lean `<` agree. [5] all three verified. SURVIVED.
- **L1.7** `IsUltrametricDist.nnnorm_tsum_eq_of_forall_lt` — `nnnorm` form of L1.6. SURVIVED (as
  L1.5).
- **L1.8** `IsUltrametricDist.norm_tsum_sub_tsum_le` — [RM] §0.1.5 *"for `f, g → 0` cofinitely,
  `‖∑' f − ∑' g‖ ≤ ⨆ i, ‖f i − g i‖`"*. Lean: `Summable f`, `Summable g`. Discharge:
  `Summable.tsum_sub` + `IsUltrametricDist.norm_tsum_le` (2 lemmas). Attacks: [2] `f = g` ✓ `0 ≤ ⨆ 0`.
  [3] summability necessary: `f` summable, `g` null non-summable in an incomplete group gives
  `‖∑' f‖` on the left, unrelated to the right. [5] verified. SURVIVED.
- **L1.9 / L1.10** `Filter.Tendsto.iSup_norm_cofinite_left` / `_right` — [RM] §0.1.4–5. Lean: for
  `f : ι × κ → E` null, `i ↦ ⨆ j, ‖f (i, j)‖` is null. Match: this is the half of *"a null family of
  null families"* read from the product. Discharge: `Metric.tendsto_nhds` /
  `Filter.eventually_cofinite`; the exceptional set `{p | ε/2 ≤ ‖f p‖}` is finite, its image under
  `Prod.fst` is finite (`Set.Finite.image`), and off it `⨆ ≤ ε/2 < ε` by `ciSup_le`
  (`Real.iSup_of_isEmpty` when `κ` is empty). Attacks: [2] `κ` empty: `⨆ = 0` ✓; `ι` empty ✓. [3] no
  ultrametric needed — stated for seminormed groups. [1] is the `⨆` honest? yes: each row is null
  (composition with the injective `(i, ·)`), hence bounded (L1.1). SURVIVED.
- **L1.11** `tendsto_cofinite_prod_of_tendsto_iSup_norm` — [RM] §0.1.5 *"a null family of null
  families sums to a null family"* (the converse packaging). Lean: rows null + row suprema null ⇒
  `f` null. Discharge: `{p | ε ≤ ‖f p‖} ⊆ ⋃_{i ∈ I_ε} {i} ×ˢ J_{i,ε}` with `I_ε` finite from `h₂`
  (`le_ciSup` needs the row bounded: L1.1 on `h₁ i`), `Set.Finite.biUnion`. Attacks: [3] `h₁`
  cannot be dropped: `f (i, j) = [i = 0] • x` has row suprema `(‖x‖, 0, 0, …)`, null, yet `f` is not
  null — so **both** hypotheses are necessary ✓. [2] empty factors ✓. SURVIVED.
- **L1.12 / L1.13** `IsUltrametricDist.tendsto_tsum_cofinite_left` / `_right` — [RM] §0.1.4 *"both
  iterated sums exist"* (the outer family is null). Discharge: `squeeze_zero_norm` with
  `IsUltrametricDist.norm_tsum_le` and L1.9. Attacks: [3] no completeness: a non-summable row
  contributes `0`. [2] ✓. SURVIVED.
- **L1.14** `IsUltrametricDist.tsum_prod_eq_tsum_tsum` — [RM] §0.1.4 *"both iterated sums exist and
  equal `∑' p, f p`"*. Discharge: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` →
  `Summable.tsum_prod'` with fibres from `Summable.prod_factor` (3 lemmas). Attacks: [3]
  completeness necessary (summability). [5] `Summable.tsum_prod'` signature checked:
  `(h : Summable f) (h₁ : ∀ b, Summable fun c ↦ f (b, c))`. SURVIVED.
- **L1.15** `IsUltrametricDist.tsum_tsum_comm` — same clause. Discharge: L1.14 twice with
  `(Equiv.prodComm ι κ).tsum_eq`; or `Summable.tsum_comm'`. SURVIVED.
- **L1.16** `tendsto_cofinite_prod_of_norm_le_mul` — [RM] §0.1.4 *"the family `b (f i) (g j)` tends
  to `0` cofinitely"*. Lean: any `b : E → F → G` with `‖b x y‖ ≤ ‖x‖ * ‖y‖` (additivity not needed).
  Discharge: `squeeze_zero_norm`; `{(i,j) | ε ≤ ‖f i‖ * ‖g j‖} ⊆ {i | ε/(C_g+1) ≤ ‖f i‖} ×ˢ
  {j | ε/(C_f+1) ≤ ‖g j‖}` (bounds from L1.1), `Set.Finite.prod`. Attacks: [2] empty index ✓. [3]
  both nullities necessary (`g ≡ y ≠ 0` constant on infinite `κ`). SURVIVED.
- **L1.17** `IsUltrametricDist.summable_prod_map₂` — Discharge: L1.16 (nullity from
  `Summable.tendsto_cofinite_zero`) + `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.
  [3] `H`, `F` need be neither ultrametric nor complete ✓. SURVIVED.
- **L1.18** `IsUltrametricDist.tsum_prod_map₂` — [RM] §0.1.4 *"its sum is `b (∑' f) (∑' g)`. Mathlib's
  `tsum_mul_tsum_of_nonarchimedean` is the case of a ring, and the module form is what the matrix
  product of §2.6 needs"*. Lean: `b : H →+ F →+ G`. Discharge: L1.14; then
  `(hg.hasSum.map (b (f i)) _).tsum_eq` with continuity from
  `AddMonoidHomClass.continuous_of_bound (b (f i)) ‖f i‖`, and the same for `b.flip (∑' g)`.
  Attacks: [4] the roadmap says "bilinear continuous"; biadditive + bound implies continuity and
  needs no scalars — more general, same content. [2] `f ≡ 0` ✓. [5] `HasSum.map` takes a continuous
  `AddMonoidHom` ✓. SURVIVED.

---

## §0.2.1, §0.2.3 The unit ball (`UnitBall.lean`)

### Plain-English proof substrate

[Sch] Lemma 1.2 (`schneider.txt:184`): *"i. `o := {a ∈ K : |a| ≤ 1}` is an integral domain with
quotient field `K`; ii. `m := {a ∈ K : |a| < 1}` is the unique maximal ideal of `o`; iii.
`o× = o ∖ m` … The assertions i.–iii. again are simple consequences of the strict triangle
inequality."* For a ring the same inequality gives the subring and the ideals, but **not** ii: the
residue ring need not be a field (erratum E2). What survives for a complete ring is the Neumann
argument: `1 − x` is a unit of `R⁰` for `‖x‖ < 1`, because `∑ xⁿ` has dominant term `1` (L1.6), so
`R⁰⁰ ⊆ Jac(R⁰)` and units are detected modulo `R⁰⁰`.

### Leaves

- **L2.1** `Subring.mem_unitClosedBall`, `norm_le_one`, `coe_unitClosedBall`,
  `unitClosedBall_toSubmonoid` — API of the definition ([RM] §0.2.1 *"The closed unit ball
  `R⁰ := {r | ‖r‖ ≤ 1}` is a subring"*). The definition is complete in the skeleton (closure under
  `+` is `norm_add_le_max`). Discharge: `mem_closedBall_zero_iff`. Attacks: [2] `R` trivial:
  excluded by `NormOneClass`. [3] `IsUltrametricDist` necessary: in `ℝ`, `1 + 1 ∉` ball ✓;
  `NormOneClass` necessary for `1 ∈`. [5] ✓. SURVIVED.
- **L2.2** `Subring.isOpen_unitClosedBall`, `isClosed_unitClosedBall` — [Wed] Example 6.13
  (`wedhorn.txt:2170`): *"`A₀ := {a ∈ A ; ‖a‖ ≤ 1}` is an open subring"*. Discharge:
  `IsUltrametricDist.isOpen_closedBall 0 one_ne_zero`, `Metric.isClosed_closedBall`. [3] open needs
  radius `≠ 0` ✓ (radius `1`). SURVIVED.
- **L2.3** `closedBallIdeal`, `openUnitBallIdeal` (proof fields) and `mem_closedBallIdeal`,
  `mem_openUnitBallIdeal` — [RM] §0.2.1 *"the open unit ball `R⁰⁰ := {r | ‖r‖ < 1}` is an ideal of
  `R⁰`"*; [Buz07] `buzzard.txt:158`: *"the ideals of `A₀` generated by `ρⁿ` … form a basis of open
  neighbourhoods of zero"*. Discharge: `norm_mul_le`, `norm_add_le_max`. Attacks: [2] `ε = 0`: the
  ideal of norm-zero elements ✓ (an ideal). [3] left ideals only are needed; commutativity not
  assumed ✓. SURVIVED.
- **L2.4** `closedBallIdeal_mono`, `closedBallIdeal_one`, `closedBallIdeal_mul_le`,
  `closedBallIdeal_le_openUnitBallIdeal` — lattice API. `mul_le` via `Ideal.mul_le`. [2] `ε > 1`:
  the ideal is `⊤` ✓ consistent. SURVIVED.
- **L2.5** `isOpen_closedBallIdeal`, `isOpen_openUnitBallIdeal`,
  `hasBasis_nhds_zero_closedBallIdeal` — Discharge: preimages of balls under the (inducing)
  inclusion; `Metric.nhds_basis_closedBall` transported to the subtype. [3] `0 < ε` necessary for
  openness. SURVIVED.
- **L2.6** `instIsLinearTopologyUnitClosedBall` — [RM] §0.2.1 (implicit in *"the topological
  nilradical of `R⁰`"*, which Mathlib defines only for a linear topology). Discharge:
  `IsLinearTopology.mk_of_hasBasis` with L2.5. Attacks: [3] stated for any `SeminormedRing` (left
  ideals), not only commutative ✓. [5] constructor verified. SURVIVED.
- **L2.7** `openUnitBallIdeal_le_topologicalNilradical` — [RM] §0.2.1 *"`R⁰⁰` is contained in the
  topological nilradical of `R⁰`"*; [Wed] Example 5.29(2) (`wedhorn.txt:1606`): *"One has
  `A° = {x ∈ A ; |x| ≤ 1}` and `A°° = {x ∈ A ; |x| < 1}`"*. Discharge:
  `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`
  in the subring. SURVIVED.
- **L2.8** `openUnitBallIdeal_eq_topologicalNilradical` — [RM] §0.2.2 *"so `R⁰ = R°` and
  `R⁰⁰ = R°°`"*. Needs `NormMulClass`: `‖aⁿ‖ = ‖a‖ⁿ → 0` forces `‖a‖ < 1`. [3] without it false
  (nilpotent of norm `1`, e.g. `ε` in `ℚ_p[ε]/(ε²)` with `‖a + bε‖ = max`). SURVIVED.
- **L2.9** `norm_one_sub_of_norm_lt_one` — [RM] §0.2.3. Discharge:
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` with `‖1‖ = 1 ≠ ‖x‖`. SURVIVED.
- **L2.10** `norm_tsum_geometric` — [RM] §0.2.3 *"`‖(1 − x)⁻¹‖ = 1`"*. Discharge: L1.6 at `i₀ = 0`:
  `‖xⁿ‖ ≤ ‖x‖ⁿ < 1 = ‖x⁰‖` (`norm_pow_le'`, `pow_lt_one₀`); summability
  `summable_geometric_of_norm_lt_one`. [2] `x = 0` ✓. SURVIVED.
- **L2.11** `norm_tsum_geometric_sub_one` — [RM] §0.2.3 *"`‖(1 − x)⁻¹ − 1‖ = ‖x‖`"*. Discharge:
  `geom_series_succ`-style split `∑' xⁿ − 1 = ∑' xⁿ⁺¹`, then L1.6 at `i₀ = 0` of the shifted family
  when `x ≠ 0` (`‖xⁿ⁺²‖ ≤ ‖x‖² < ‖x‖`), and `x = 0` separately. Attacks: [3] submultiplicative norm
  suffices — `‖x‖ⁿ⁺² < ‖x‖` needs only `0 < ‖x‖ < 1` ✓. SURVIVED.
- **L2.12** `isUnit_of_norm_one_sub_lt_one` — [RM] §0.2.3. Discharge: `mul_neg_geom_series`,
  `geom_series_mul_neg`; the inverse lies in `R⁰` by L2.10. [3] no commutativity ✓. SURVIVED.
- **L2.13** `isUnit_iff_isUnit_mk` — [RM] §0.2.3 *"the units of `R⁰` are exactly the elements of `R⁰`
  whose image in `R⁰/R⁰⁰` is a unit"*. Discharge: `⇐`: lift the inverse, `a b = 1 − x`, L2.12,
  `isUnit_of_mul_isUnit_left`. [3] commutativity used (quotient ring; units from a product).
  [SRC] `PowerBounded.isUnit_iff_isUnit_mk_topologicalNilradical`. SURVIVED.
- **L2.14** `openUnitBallIdeal_le_jacobson_bot` — **corrected clause** (erratum E2). [RM] §0.2.3
  claimed *"`R⁰⁰` is the unique maximal ideal of `R⁰` when the norm is multiplicative"*.
  **Attack [1] succeeded on the roadmap's form**: `R = ℚ_p⟨X⟩`, Gauss norm (multiplicative):
  `R⁰ = ℤ_p⟨X⟩`, `R⁰⁰ = pℤ_p⟨X⟩`, `R⁰/R⁰⁰ = 𝔽_p[X]` is not a field. What is true: `R⁰⁰ ⊆ Jac(R⁰)`.
  Discharge: `Ideal.mem_jacobson_bot` + L2.12 (`‖x y‖ < 1`). SURVIVED in corrected form.
- **L2.15** `isUnit_iff_norm_eq_one`, `instIsLocalRingUnitClosedBall`,
  `maximalIdeal_unitClosedBall` — [Sch] Lemma 1.2 ii–iii (quoted above). For a normed *field*, no
  completeness. Discharge: `norm_inv`, `IsLocalRing.of_nonunits_add`, `IsLocalRing.mem_maximalIdeal`.
  [2] trivially valued field: `R⁰ = K`, `R⁰⁰ = 0` ✓ consistent. SURVIVED.

---

## §0.2.1–§0.2.2 Power-bounded and topologically nilpotent elements (`PowerBounded.lean`)

### Plain-English proof substrate

[Wed] Definition 5.27 (`wedhorn.txt:1589`): *"A subset `B` of `A` is called bounded if for every
neighborhood `U` of `0` in `A` there exists an open neighborhood `V` of `0` in `A` such that
`vb ∈ U` for all `v ∈ V` and `b ∈ B`. An element `x ∈ A` is called power-bounded if the set
`{xⁿ ; n ≥ 1}` is bounded."* Example 5.29(2) (`:1606`): for a height-one valuation *"a subset `B`
… is bounded if and only if there exists `C > 0` such that `|x| < C` … One has
`A° = {x ∈ A ; |x| ≤ 1}` and `A°° = {x ∈ A ; |x| < 1}`."* Norm-bounded ⇒ bounded needs only
submultiplicativity (`V` = a small ball); the converse divides by a small nonzero `v`, which needs
a multiplicative norm and a nonzero `v` near `0`.

### Leaves

- **L3.0** `TopologicalRing.IsBounded`, `PowerBounded.IsPowerBounded` — **seam definitions**,
  verbatim from mathlib4#40013 (`pr40013.diff` lines 65 and 173). [4] ⚠ the PR's powers are
  `n : ℕ` including `n = 0`, [Wed]'s are `n ≥ 1`; the two agree because `{1}` is bounded.
- **L3.1** `isBounded_of_forall_norm_le` — Discharge: `Metric.mem_nhds_iff`; `V := ball 0
  (ε / (max C 0 + 1))`; `norm_mul_le`. [2] `S = ∅`, `C < 0` ✓ (`max C 0`). SURVIVED.
- **L3.2** `isPowerBounded_of_norm_pow_le`, `isPowerBounded_of_norm_le_one` — [RM] §0.2.1 *"Every
  element of `R⁰` is power-bounded"*. `C := max ‖1‖ 1`; `norm_pow_le'` for `n ≥ 1`. [3] **no
  `NormOneClass`** (the [SRC] form assumes it; `‖1‖` is just a constant). SURVIVED.
- **L3.3** `IsBounded.exists_norm_le` — Discharge: `U := ball 0 1`; `NeBot (𝓝[≠] 0)` yields
  `v ∈ V`, `v ≠ 0` (`Filter.NeBot.nonempty_of_mem` on `V ∩ {0}ᶜ`); `norm_mul`. [3] both hypotheses
  necessary — the roadmap's two counterexamples (L12.7, L12.8). SURVIVED.
- **L3.4** `IsPowerBounded.norm_le_one`, `isPowerBounded_iff_norm_le_one` — [RM] §0.2.2. If
  `1 < ‖a‖` then `‖aⁿ‖ = ‖a‖ⁿ` is unbounded (`tendsto_pow_atTop_atTop_of_one_lt`). [3] `NormOneClass`
  not assumed: `‖a ^ (n+1)‖ = ‖a‖ ^ (n+1)` by induction from `norm_mul`. SURVIVED.
- **L3.5** `IsTopologicallyNilpotent.of_norm_lt_one`, `.norm_lt_one`,
  `isTopologicallyNilpotent_iff_norm_lt_one` — [RM] §0.2.1–2. `of_norm_lt_one` **is** Mathlib's
  `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` under the definitional unfolding; converse:
  `‖x‖ⁿ → 0` forces `‖x‖ < 1`. [3] converse needs `NormMulClass` (L2.8's counterexample), not
  `NeBot` ✓. SURVIVED.

---

## §0.2.4 Multiplicative elements (`Multiplicative.lean`)

### Plain-English proof substrate

[JN] `jn.txt:487`: *"We say that `r ∈ R` is multiplicative if `|rs| = |r||s|` for all `s ∈ R`."*
`:496`: *"a unit `ϖ` in a normed ring `R` is multiplicative if and only if `|ϖ⁻¹| = |ϖ|⁻¹`."*
`:519`: *"if `r ∈ R` is a multiplicative unit, then one sees easily that `‖rm‖ = |r|·‖m‖` for all
`m ∈ M`."* [Bel] Exercise II.1.1 (`bellaiche.txt:1963`): *"An element `x` in `R*` is called
multiplicative for `| |` if `|x||x⁻¹| = 1`. Show that `x` is multiplicative if and only if for all
`y ∈ R`, `|xy| = |x||y|`."* One sandwich proves everything:
`‖m‖ = ‖u⁻¹ • u • m‖ ≤ ‖u⁻¹‖ ‖u • m‖ = ‖u‖⁻¹ ‖u • m‖ ≤ ‖m‖`.

### Leaves

- **L4.1** `IsMultiplicative.mul`, `.norm_pow_mul`, `.one`, `.norm_pow`, `.pow`,
  `isMultiplicative_of_normMulClass` — [RM] §0.2.4 *"Products and powers of multiplicative elements
  are multiplicative"*. [SRC] `00_Tate.IsMultiplicative.*`. [2] `n = 0`: `pow` and `norm_pow` need
  `‖1‖ = 1` ([3] necessary: in a ring with `‖1‖ = 2`, `‖a⁰ · x‖ = ‖x‖ ≠ 2‖x‖`); `norm_pow_mul` does
  not ✓ — hypotheses placed accordingly. SURVIVED.
- **L4.2** `isMultiplicative_units_iff` — [JN] `:496`, [Bel] Ex. II.1.1 (quoted). `⇒`: `x := u⁻¹`
  and `‖1‖ = 1`. `⇐`: the sandwich; positivity of `‖u‖` from `1 = ‖u u⁻¹‖ ≤ ‖u‖ ‖u⁻¹‖`. [2] is
  `‖u‖ = 0` possible (seminorm)? then `‖u⁻¹‖ = 0⁻¹ = 0` and `1 ≤ 0`, contradiction — so the iff is
  safe for seminorms ✓. SURVIVED.
- **L4.3** `IsMultiplicative.norm_pos`, `.norm_inv`, `.inv`, `.zpow`, `.norm_zpow` — unit API.
  `zpow` by `Int.induction_on`. SURVIVED.
- **L4.4** `IsMultiplicative.norm_smul`, `.norm_zpow_smul` — [JN] `:519` (quoted). Discharge:
  `norm_smul_le` twice (the sandwich). [SRC] `01_OperatorNorm.norm_pseudoUniformizer_smul`. [3]
  seminormed `M` suffices ✓; `IsBoundedSMul` necessary. SURVIVED.

---

## §0.3.1–§0.3.2 Module constructions (`Module.lean`)

- **L5.1** `Prod.instIsUltrametricDist` — [RM] §0.3.1 *"finite products with the max norm"*.
  `Prod.dist_eq`, `max_le_max`. [5] absence verified by a failing `inferInstance`. SURVIVED.
- **L5.2** `Submodule.instIsBoundedSMul` — [RM] §0.3.1 *"a closed submodule with the restricted
  norm"*. The two `IsBoundedSMul` fields restrict. [5] absence verified. SURVIVED.
- **L5.3** `QuotientAddGroup.instIsUltrametricDist`, `Submodule.Quotient.…`, `Ideal.Quotient.…` —
  [RM] §0.3.1 *"the quotient norm `‖x + N‖ = inf ‖x + n‖`, which is again ultrametric and
  complete"*; [Sch] §5.B (`schneider.txt:975`): *"for any seminorm `q` on `V` one has the quotient
  seminorm `q(v + U) := inf_{u ∈ U} q(v + u)`"*; Prop 8.3 (`:2281`). Discharge:
  `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`; representatives within `ε` from
  `QuotientAddGroup.norm_lt_iff`; `le_of_forall_pos_lt_add`. Completeness is Mathlib
  (`Submodule.Quotient.completeSpace`). [2] `S = ⊤` ✓, `S = ⊥` ✓. SURVIVED.
- **L5.4** `AddEquiv.completeSpace_congr_of_bounds` — [RM] §0.3.2 *"bounded-equivalent norms have
  the same bounded maps and the same Cauchy sequences"*; [Sch] proof of Prop 10.1: the rescaled
  norm *"defines the same topology"*. Discharge: `AddMonoidHomClass.lipschitz_of_bound` both ways →
  a `UniformEquiv` → `completeSpace_congr` (or `IsUniformEmbedding`). [2] `C < 0` forces all norms
  `0`; both sides then complete ✓. [4] "same bounded maps" is composition and is not given a
  declaration. SURVIVED.

---

## §0.4.1–§0.4.4 Tate normed rings (`Tate.lean`)

### Plain-English proof substrate

[JN] Definition 2.1.2 (`jn.txt:489`): *"Let `R` be a normed ring. We say that `R` is Tate if `R`
contains a multiplicative unit `ϖ` such that `|ϖ| < 1`. We call such a `ϖ` a multiplicative
pseudo-uniformizer. If `R` is also complete, we say that `R` is a Banach–Tate ring. If `R` is a
Tate normed ring and `ϖ` is a multiplicative pseudo-uniformizer, then we define the corresponding
valuation `v_ϖ` on `R` by `v_ϖ(r) = −log_a |r|`, where `a = |ϖ⁻¹|`."* [JN]'s normed rings satisfy
`|1| = 1` (Definition 2.1.1, `:475`), which is `NormOneClass`. [Buz07] `buzzard.txt:156`: *"Fix once
and for all `ρ ∈ K×` with `|ρ|_K < 1` … We use `ρ` to 'normalise' vectors in several proofs."*
The scaling trick: the intervals `(δ cⁿ⁺¹, δ cⁿ]`, `c = ‖ϖ‖`, partition `(0, ∞)`, and
`‖ϖⁿ • m‖ = cⁿ ‖m‖` exactly (L4.4).

### Leaves

- **L6.0** `PseudoUniformizer`, `IsTate`, the coercion (`coe_unit` removed 2026-09-29: the coercion unfolds at elaboration, so it was a syntactic tautology flagged by `synTaut`) — definitions ([JN] Def 2.1.2,
  quoted). [3] the structure has no positivity field; **erratum E5**: [RM] §0.4.1 *"A Tate normed
  ring is nontrivial"* fails for the zero ring (the unit `0 = 1` has norm `0 < 1` and is
  multiplicative); under `[NormOneClass R]` — [JN]'s standing `|1| = 1` — it is
  `NormOneClass.nontrivial`. [SRC] `00_Tate.PseudoUniformizer.norm_pos` records the same remark.
- **L6.0b** `normOneClass_of_nontrivial` — result of attack [3] on E5 (*is `[NormOneClass R]`
  minimal?*), made while cross-checking `Suggested.lean`, whose `val_self` assumes `[Nontrivial R]`
  instead. Given a pseudo-uniformiser the two hypotheses are **equivalent**: `‖ϖ‖ = ‖ϖ * 1‖ =
  ‖ϖ‖ * ‖1‖` (multiplicativity at `x = 1`) and `‖ϖ‖ ≠ 0` (a unit of a nontrivial ring is nonzero and
  the norm of a `NormedRing` is definite) give `‖1‖ = 1`; conversely `‖1‖ = 1` gives `1 ≠ 0`. Source:
  [JN] Def 2.1.1(1) (`jn.txt:476`, *"`|1| = 1`"*). Decision: keep `[NormOneClass R]` on the lemmas —
  it is the sources' hypothesis and lets the `IsMultiplicative` API fire by instance — and state
  the equivalence once as a theorem (it depends on `ϖ`, so it cannot be an instance). [1] the zero
  ring: `Nontrivial` fails ✓ consistent. [2] seminormed rings: false there (`‖ϖ‖` may be `0`), and
  `PseudoUniformizer` is only defined for `NormedRing` ✓. Discharge: `mul_one`,
  `norm_ne_zero_iff`, `Units.ne_zero`, `mul_right_eq_self₀`; proof compiled in
  `scratch/spot2.lean`. SURVIVED.
- **L6.1** `norm_pos`, `norm_inv`, `norm_zpow`, `log_norm_neg`, `norm_smul`, `norm_zpow_smul` —
  [RM] §0.4.1 *"`‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`"*. One-line consequences of L4.3–L4.4 at `u := ϖ.unit`;
  `Real.log_neg`. [3] all need `NormOneClass` (positivity). SURVIVED.
- **L6.2** `existsUnique_zpow_norm_smul_mem_Ioc` — [RM] §0.4.2 *"For `ϖ : PseudoUniformizer R` and
  `m ≠ 0` in a normed `R`-module, there is a unique `n : ℤ` with `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1`"*. Lean:
  general shell `Set.Ioc (δ * ‖ϖ‖) δ`, `0 < δ` — **more general than the roadmap**, because Layer 1
  scales into the shell `(δ‖ϖ‖, δ]` of a continuity modulus ([SRC] `01_OperatorNorm.le_opNorm`).
  Discharge: `norm_zpow_smul`; `exists_mem_Ioc_zpow` at base `‖ϖ‖⁻¹ > 1` applied to `δ / ‖m‖`;
  uniqueness from `zpow_lt_zpow_iff_right₀`. Attacks: [2] `‖m‖ = δ`: `n = 0` ✓ (`Ioc` closed on the
  right). [3] `m ≠ 0` and `NormedAddCommGroup M` necessary (`‖m‖ > 0`); uniqueness fails for
  `m = 0`. [4] the roadmap shell is the case `δ = 1` = L6.3. SURVIVED.
- **L6.3** `existsUnique_zpow_norm_smul_mem_Ioc_one` — the roadmap's literal form; `one_mul`.
- **L6.4** `val` (definition), `val_zero`, `val_of_ne_zero`, `val_eq_top_iff` — [JN] Def 2.1.2
  (quoted): `−log_a |r|` with `a = |ϖ⁻¹|` is `log ‖r‖ / log ‖ϖ‖`. [4] sign check: `r = ϖ` gives `1` ✓.
  `⊤` at `0` is [RM] §0.4.3 (*"with `val ϖ 0 = ⊤`"*), so the value is never junk. SURVIVED.
- **L6.5** `val_self`, `val_one`, `val_zpow_self` — [RM] §0.4.3 *"so that `val ϖ ϖ = 1`"*.
  `div_self (log_norm_neg).ne`, `Real.log_one`, `Real.log_zpow`. [3] `NormOneClass` necessary
  (`log ‖ϖ‖ ≠ 0`, `‖1‖ = 1`). SURVIVED.
- **L6.6** `val_le_val_iff`, `val_lt_val_iff`, `val_nonneg_iff` — [RM] §0.4.3 *"order-reversing in
  the norm"*. Cases on `r = 0`, `s = 0`; `div_le_div_right_of_neg`, `Real.log_le_log_iff`.
  Attacks: [2] all four zero/nonzero combinations checked by hand: `r = 0`: `⊤ ≤ val s ↔ s = 0 ↔
  ‖s‖ ≤ 0 = ‖r‖` ✓. SURVIVED.
- **L6.7** `val_add_val_le_val_mul`, `val_mul`, `min_val_le_val_add` — [RM] §0.4.3 *"`val ϖ (r * s) ≥
  val ϖ r + val ϖ s` with equality when the norm is multiplicative, `val ϖ (r + s) ≥ min`"*. [2]
  `r s = 0` with `r, s ≠ 0`: right side `⊤` ✓. [4] ⚠ not an `AddValuation` — no bundled structure
  is introduced ([RM], same clause). SURVIVED.
- **L6.8** `norm_eq_rpow_of_val_eq` — [RM] §0.4.3 *"`‖r‖ = ‖ϖ‖ ^ (val ϖ r)`"*.
  `Real.rpow_def_of_pos`, `Real.exp_log`. SURVIVED.
- **L6.9** `ofNormedAlgebra` (proof fields), `isTate_of_normedAlgebra`, the field instance — [RM]
  §0.4.4; [Wed] Example 6.13 (`wedhorn.txt:2170`): *"Every normed `k`-algebra `(A, ‖·‖)` is a Tate
  ring: `A₀ := {a ∈ A ; ‖a‖ ≤ 1}` is an open subring and if `r ∈ k×` is any element with
  `v(r) < 1`, then `(rⁿ A₀)ₙ` is a fundamental system of neighborhoods of `0` in `A₀`."* Discharge:
  `Algebra.smul_def`, `norm_smul`, `norm_algebraMap'`, `NormedField.exists_norm_lt_one`. [3]
  `NormOneClass R` necessary (`‖c • 1‖ = ‖c‖`). [SRC] `00_Tate.isTate_of_normedAlgebra`. SURVIVED.
- **E6 (external).** [RM] §0.4.3 *"`val ϖ` is the real additive valuation `normAddVal` … rescaled"*:
  `normAddVal` is Newton-polygons Layer 1 and not in this chain. Not ticketed; recorded in
  `plan.md`.

---

## §0.3.2 Comparison of norms (`NormComparison.lean`)

### Plain-English proof substrate ([JN] Lemmas 2.1.6–2.1.7, `jn.txt:565–640`, read in full)

[JN] Lemma 2.1.6: *"Let `R` be a complete Tate ring, and let `ϖ, π ∈ R` be topologically nilpotent
units. Assume that we have two equivalent norms `|−|_ϖ` and `|−|_π` on `R` … such that `ϖ` is
multiplicative for `|−|_ϖ` and `π` is multiplicative for `|−|_π`. Then we may find constants
`C₁, C₂, s > 0` such that, if `|a|_π < 1`, `|a|_ϖ ≤ C₁`, and if `|a|_π ≥ 1`, then
`|a|_ϖ ≤ C₂ |a|_π^s`."* Proof: `D₁ < 1` with `|a|_π ≤ D₁ ⇒ |a|_ϖ ≤ 1`; `m` with `|ϖᵐ|_π ≤ D₁`;
`C₁ = |ϖ|_ϖ^{−m}`; for `|a|_π ≥ 1`, `n = ⌈log|a|_π / log|ϖᵐ|_π⁻¹⌉`, `|ϖ^{mn} a|_π ≤ 1`, so
`|a|_ϖ ≤ C₁^{n+1} ≤ C₂ |a|_π^s` with `s = log C₁ / log |ϖᵐ|_π⁻¹`, `C₂ = C₁²`. The proof **never uses
`π`**, and proves the first bound for `|a|_π ≤ 1`. Lemma 2.1.7: a common `ϖ`, `s` from
`|ϖ|₂ = |ϖ|₁^s`; with `n` as before, `|ϖ^{−m(n−1)}|₁ < |a|₁ ≤ |ϖ^{−mn}|₁`, so
`|a ϖ^{m(n+1)}|₁ ≤ D₁`, `|a|₂ ≤ |ϖ|₂^{−m(n+1)} ≤ C₂ |a|₁^s`; *"Swapping `|−|₁` and `|−|₂` we get
a similar inequality."* The upper bound uses only continuity of the identity `(R,|·|₁) → (R,|·|₂)`
and multiplicativity of `ϖ` for `|·|₂` — no inverse.

### Leaves

- **L7.1** `exists_norm_le_of_norm_map_le_one` — [JN] 2.1.6, first bound (quoted), in the form
  proved (`≤ 1`). Lean: `e : R ≃+* S`, `he`, `he'`, `ϖ`; no `π`. Discharge: `D₁` from
  `Metric.continuousAt_iff` for `e.symm` at `0`; `m` from `he` and L10.1-style decay of `ϖᵐ`;
  L6.1. Attacks: [3] `π` unused ([SRC] carries a `nolint` for it) — dropped; `he` is used (for `m`)
  and `he'` is used (for `D₁`); neither can go. [4] `≤ 1` vs. [JN]'s `< 1`: stronger ✓. SURVIVED.
- **L7.2** `exists_norm_le_mul_rpow_norm_map` — second bound. `n := ⌈log ‖e a‖ / log (‖e ϖᵐ‖⁻¹)⌉`
  (`Int.ceil`), `Real.rpow_natCast`, `Real.rpow_le_rpow_left_iff`; constants as [JN]. [2]
  `‖e a‖ = 1`: `n = 0` ✓. [1] is `s` allowed to depend on `m`? yes, existential. SURVIVED.
- **L7.3** `logb_norm_map_pos` — [JN] 2.1.7 *"`s` is determined by `|ϖ|₂ = |ϖ|₁^s`"*. Lean:
  `0 < Real.logb ‖ϖ‖ ‖e ϖ‖` for a continuous ring hom `e` with `e ϖ` multiplicative. Discharge:
  `Real.logb_pos_iff_of_base_lt_one`; `‖e ϖ‖ < 1` because `‖e ϖ‖ⁿ = ‖e (ϖⁿ)‖ → 0` (continuity +
  L4.1 `norm_pow`); `0 < ‖e ϖ‖` by L4.3 on `Units.map e ϖ.unit`. [3] **`‖e ϖ‖ < 1` is derived, not
  assumed** ([SRC] assumes it). SURVIVED.
- **L7.4** `exists_norm_map_le_mul_rpow` — [JN] 2.1.7 upper bound, for a continuous
  **homomorphism**. Proof re-derived above; `a = 0`: `Real.zero_rpow (ne_of_gt L7.3)`. Attacks: [1]
  sanity instance `S = R` with norm `‖·‖²` on a field: `s = 2`, `C = 1` ✓. [3] bijectivity never
  used; `NormOneClass S` used (positivity of `‖e ϖ‖`). [2] `e` cannot be `0` (`e 1 = 1`, `S`
  nontrivial). SURVIVED.
- **L7.5** `exists_mul_rpow_le_norm_map` — lower bound, by L7.4 applied to `e.symm` and the
  pseudo-uniformiser `⟨Units.map e ϖ.unit, hϖ, _⟩` of `S`; exponents are inverse
  (`Real.inv_logb`). [3] needs `he'` ✓ and `NormOneClass R` ✓. SURVIVED.

---

## §0.3.3 The rescaled norm (`Rescale.lean`)

### Plain-English proof substrate

[Sch] proof of Prop 10.1 (`schneider.txt:2953`): *"we always can replace a given defining norm
`‖ ‖′` by the norm `‖v‖ := inf {s ∈ |K| : s ≥ ‖v‖′}` which, because of `r ≤ ‖v‖′/‖v‖ ≤ 1`, defines
the same topology."* [Bel] proof of Thm II.1.13 (`bellaiche.txt:2109`): *"Set
`|m|′ = inf_{r ∈ p^ℤ, r ≥ |m|} r`. Then `| |′` is a norm on `M` which is equivalent to `| |` and
satisfies Hypothesis II.1.11."* [Col10] `colmez.txt:129`: *"`v′_B(x) = v_p(π_L) · [v_B(x)/v_p(π_L)]`
est une valuation sur `B`, équivalente à `v_B`, à valeurs dans `v_p(L)`."* For `0 < c < 1` the
qualifying exponents are `n ≤ logb c x`, so the infimum is `c ^ ⌊logb c x⌋`.

### Leaves

- **L8.1** `zpowCeil_nonneg`, `zpowCeil_of_nonpos`, `zpowCeil_of_pos`, `le_zpowCeil`,
  `mul_zpowCeil_lt`, `zpowCeil_le_of_le_zpow` — the closed form and the two [Sch] inequalities.
  Discharge: `Real.sInf_nonneg`; `csInf_le`/`le_csInf`; `x ≤ c ^ n ↔ (n : ℝ) ≤ logb c x` from
  `Real.rpow_logb`, `Real.rpow_le_rpow_left_iff_of_base_lt_one`; `Int.floor_le`,
  `Int.lt_floor_add_one`. Attacks: [2] `x ≤ 0`: every `n` qualifies, `inf = 0` ✓ (`c ^ n → 0`); [4]
  [Sch]'s `r ≤ ‖v‖′/‖v‖` is `c * zpowCeil ≤ x`; ours is **strict** (`c ^ (N+1) < x` since
  `N + 1 > logb c x`) ✓ stronger. [5] ⚠ `Real.logb_zpow` does not exist; use `Real.logb_rpow` with
  `Real.rpow_intCast`. SURVIVED.
- **L8.2** `exists_zpowCeil_eq_zpow`, `zpowCeil_zpow`, `zpowCeil_pos`, `zpowCeil_eq_zero_iff`,
  `zpowCeil_mono`, `zpowCeil_max`, `zpowCeil_zpow_mul`, `zpowCeil_mul_le` — algebra of `zpowCeil`.
  `mono`: the qualifying set shrinks; `max`: `Monotone.map_max`; `zpow_mul`: `logb` shifts by `n`;
  `mul_le`: L8.1 minimality at `c ^ (N + M)`. **Attack [1] found a false neighbour**: `zpowCeil` is
  **not subadditive** — `c = 1/2`: `zpowCeil 0.51 = 1 > 1/2 + 1/64`. So the rescaled norm exists
  only for ultrametric `M` (`max`, not `+`); recorded in the module docstring. SURVIVED.
- **L8.3** `rescaledNorm` (four proof fields), `norm_toRescaled` (`rfl`),
  `norm_le_norm_toRescaled`, `norm_mul_norm_toRescaled_lt`, `exists_norm_rescaled_eq_zpow`,
  `norm_toRescaled_eq_of_forall_exists_zpow` — [RM] §0.3.3 *"a norm taking values in `‖π‖ ^ ℤ ∪ {0}`,
  ultrametric, with `‖π‖ ‖m‖' < ‖m‖ ≤ ‖m‖'`"*. `add_le'`: `zpowCeil_mono` ∘ `norm_add_le_max`, then
  `max ≤ +`. [3] `IsUltrametricDist M` necessary (L8.2's attack); `NormOneClass R` for `0 < ‖ϖ‖`.
  [2] the strict inequality needs `m ≠ 0` ✓ (hypothesis). SURVIVED.
- **L8.4** `IsUltrametricDist (Rescaled ϖ M)`, `CompleteSpace (Rescaled ϖ M)`,
  `norm_smul_rescaled` — [RM] §0.3.3 *"complete when the original is, and with
  `‖π • m‖' = ‖π‖ ‖m‖'`"*. Completeness: L5.4 with `e := toRescaled`, `C = ‖ϖ‖⁻¹`, `C' = 1`.
  `norm_smul`: L6.1 + `zpowCeil_zpow_mul` at `n = 1`. SURVIVED.
- **L8.5** `isBoundedSMul_rescaled` — **erratum E3**. [RM] §0.3.3 says *"on any normed `R`-module"*.
  **Attack [1] succeeded on the unrestricted form**: `R = M = ℂ_p`, `ϖ = p`, `‖r‖ = p^{-1/2}`:
  `‖r • 1‖' = 1 > p^{-1/2} = ‖r‖ ‖1‖'`. With `∀ r ≠ 0, ∃ n, ‖r‖ = ‖ϖ‖ ^ n` ([Bel] Hypothesis II.1.11:
  *"the set of non-zero norms `|R*|` is the discrete subgroup `|π|^ℤ`"*, `bellaiche.txt:2076`):
  `‖r • m‖ ≤ ‖r‖ ‖m‖' = c^{k+N}`, minimality (L8.1). A theorem, not an instance. SURVIVED in
  restricted form.

---

## §0.3.4 Residue rings and modules (`Residue.lean`)

### Plain-English proof substrate

[Bel] §II.1.4 (`bellaiche.txt:2078`): *"We denote by `R⁰` the set of elements `r` of `R` such that
`|r| ≤ 1`, which is a subring of `R`, and by `R̃` the quotient ring `R⁰/πR⁰`. For `M` a Banach
`R`-module we define `M⁰ = {m ∈ M, |m| ≤ 1}`, which is an `R⁰`-submodule of `M`, and
`M̃ = M⁰/πM⁰`, which is a `R̃`-module."* [Sch] proof of Prop 10.1: *"Since `m · B₁(0) ⊆ B₁⁻(0)` the
`o`-module quotient `V̄ := B₁(0)/B₁⁻(0)` is a `k`-vector space."* The identity `π M⁰ = {‖m‖ ≤ ‖π‖}`
holds always (`m = π • (π⁻¹ • m)`, L4.4); it equals the open ball exactly when no norm lies in
`(‖π‖, 1)`.

### Leaves

- **L9.1** `Submodule.unitClosedBall` (proof fields), `mem_unitClosedBall` — [Bel] (quoted).
  `norm_smul_le`, `norm_add_le_max`. [3] no commutativity, seminorms suffice ✓. SURVIVED.
- **L9.2** `toUnitClosedBall_mem_ideal`, `mem_ideal_iff`, `ideal_eq_closedBallIdeal`,
  `ideal_le_openUnitBallIdeal` — [RM] §0.4.5 at `n = 1`. `Ideal.mem_span_singleton`; `⇐`: the
  quotient `ϖ⁻¹ a` has norm `‖a‖/‖ϖ‖ ≤ 1` (L4.3 `inv`). [3] multiplicativity necessary: a
  non-multiplicative unit `u` of norm `< 1` can have `‖u⁻¹ a‖ > 1`. SURVIVED.
- **L9.3** `ideal_eq_openUnitBallIdeal` — under `∀ r ≠ 0, ∃ n, ‖r‖ = ‖ϖ‖ ^ n`: `‖a‖ = cⁿ < 1` forces
  `n ≥ 1` (`zpow_lt_one_iff_right_of_lt_one₀`-type), so `‖a‖ ≤ c`. [2] `a = 0` ✓. SURVIVED.
- **L9.4** `ResidueRing`, `ResidueModule` (abbrevs; the `Module` instance is found by
  `inferInstance` — checked in the skeleton, needs `Mathlib.Algebra.Module.Torsion.Basic`).
- **L9.5** `mem_ideal_smul_top_iff` — `π M⁰ = {m ∈ M⁰ | ‖m‖ ≤ ‖π‖}`, **for every `M`**. `⇒`:
  `Submodule.smul_induction_on` + ultrametric sums; `⇐`: `Submodule.smul_mem_smul` with
  `ϖ⁻¹ • m ∈ M⁰`. SURVIVED.
- **L9.6** `mem_ideal_smul_top_iff_norm_lt_one` — [RM] §0.3.4 *"if the norm of `M` takes values in
  `‖π‖ ^ ℤ ∪ {0}` then `π M⁰ = {m | ‖m‖ < 1}`"*. L9.5 + the argument of L9.3. [3] the value
  hypothesis necessary (`ℂ_p`, L12.6). SURVIVED.

---

## §0.4.5 The bridge to Huber (`Huber.lean`) — MILESTONE M1

### Plain-English proof substrate

[JN] Remark 2.1.3(1) (`jn.txt:500`): *"The underlying topological ring is a Tate ring in the
language of Huber; the unit ball `R₀` is a ring of definition and `ϖ` is a topologically nilpotent
unit."* [Wed] Def 6.1(ii) (`wedhorn.txt:2059`): *"`A` contains an open subring `A₀` such that the
subspace topology on `A₀` is `I`-adic, where `I` is a finitely generated ideal of `A₀`"*; Def 6.10:
*"A topological ring is called Tate ring if it is f-adic and has a topologically nilpotent unit."*
[Buz07] `buzzard.txt:158`: *"the ideals of `A₀` generated by `ρⁿ`, `n = 1, 2, …`, form a basis of
open neighbourhoods of zero in `A`."* Everything follows from
`(ϖ)ⁿ = (ϖⁿ) = {a ∈ R⁰ | ‖a‖ ≤ ‖ϖ‖ⁿ}` (L9.2 for the multiplicative unit `ϖⁿ`).

### Leaves

- **L10.1** `isTopologicallyNilpotent` — L3.5 at `‖ϖ‖ < 1`. SURVIVED.
- **L10.2** `mem_ideal_pow_iff`, `ideal_pow_eq_closedBallIdeal`, `ideal_fg` — [RM] §0.4.5 *"the
  ideal powers are the norm balls, `ϖⁿ R⁰ = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`"*. `Ideal.span_singleton_pow`;
  L9.2's argument for `ϖⁿ` (L4.1 `pow`, L4.3). [2] `n = 0`: `⊤` and `‖a‖ ≤ 1` ✓. `ideal_fg`:
  `Submodule.fg_span_singleton`. [SRC] `00_TateRings.mem_ideal_pow`. SURVIVED.
- **L10.3** `isAdic_ideal` — [RM] §0.4.5 *"the `(ϖ)`-adic topology of `R⁰` is the norm topology"*.
  `isAdic_iff`: powers open (L2.5, `‖ϖ‖ⁿ > 0`) and cofinal (`‖ϖ‖ⁿ → 0`,
  `tendsto_pow_atTop_nhds_zero_of_lt_one`). [5] `isAdic_iff` needs `IsTopologicalRing R⁰` — the
  subring instance exists ✓. SURVIVED.
- **L10.4** `exists_pow_mul_mem_unitClosedBall` — [Wed] Prop 6.14 (`:2176`): *"For every `a ∈ A`
  there exists `n ∈ ℕ` such that `a sⁿ ∈ B`, hence `A = B_s`."* `‖ϖⁿ a‖ = ‖ϖ‖ⁿ ‖a‖ → 0`. SURVIVED.
- **L10.5** `hasBasis_nhds_zero_smul_unitClosedBall` — [Wed] Example 6.13 (quoted at L6.9).
  `ϖⁿ • R⁰ = closedBall 0 (‖ϖ‖ⁿ)` by L4.4; `Metric.nhds_basis_closedBall` refined along `‖ϖ‖ⁿ → 0`.
  This is the hypothesis shape of `GaugeNorm.lean` (plan decision 6). SURVIVED.
- **L10.6** `isPowerBounded_of_mem_unitClosedBall` — [RM] §0.2.1; L3.2. SURVIVED.
- **L10.7** `gaugeNorm_unitClosedBall` — **planner's addition**: the gauge norm of `(R⁰, ϖ)` at
  `a = ‖ϖ‖⁻¹` is `zpowCeil ‖ϖ‖ ‖r‖`. Both are `inf {‖ϖ‖ⁿ | ‖r‖ ≤ ‖ϖ‖ⁿ}` once
  `r ∈ ϖⁿ • R⁰ ↔ ‖r‖ ≤ ‖ϖ‖ⁿ` (L10.5's computation) and `(‖ϖ‖⁻¹) ^ (-n) = ‖ϖ‖ ^ n`. Source: [JN]
  Remark 2.1.3(1) read against [RM] §0.3.3; it is the precise sense in which the two bridges are
  inverse "up to [JN] Lemma 2.1.7". [2] `r = 0`: both `0` ✓. [1] equality with the *original* norm
  would be false (`ℂ_p`) — the statement is with `zpowCeil`, correctly. SURVIVED.
- **E7 (seam).** No `PairOfDefinition` here; L2.2, L10.2 (`ideal_fg`), L10.3, L10.1 are its four
  fields plus the Tate condition.

---

## §0.4.6 The gauge norm (`GaugeNorm.lean`) — MILESTONE M2

### Plain-English proof substrate

[JN] Remark 2.1.3(1) (`jn.txt:502`): *"Conversely, assume `R` is a Tate ring and `ϖ ∈ R` is a
topologically nilpotent unit, contained in some ring of definition `R₀`. If `a ∈ ℝ_{>1}`, then we
may define a norm on `R` by `|r| = inf {a^{−n} | r ∈ ϖⁿR₀, n ∈ ℤ}`. Equipped with this norm, `R` is
a Tate normed ring with unit ball `R₀` and `ϖ` is a multiplicative pseudo-uniformizer."* [Wed]
Prop 6.14 / Cor 6.15 (`wedhorn.txt:2176–2191`): for such `(R₀, ϖ)`, `(ϖⁿ R₀)ₙ` is a fundamental
system of neighbourhoods of `0` — the hypothesis `hbasis`. The exponent set
`E(r) = {n | r ∈ ϖⁿ A₀}` is a down-set (`ϖ ∈ A₀`), nonempty (multiplication by `r` is continuous
at `0`), and bounded above unless `r ∈ ⋂ ϖⁿ A₀`; so `N r = a^{−max E}` or `0`, and every property
is a property of `max E`. [JN] gives no proof; this expansion is the substrate.

### Leaves

- **L11.1** `gaugeNorm_nonneg`, `exists_mem_zpow_smul` — absorption. Attack [3] **removed a
  hypothesis**: the first draft used `ϖᵏ → 0`, which needs `ϖ ∈ A₀`; instead
  `(· * r)` is continuous at `0` and `A₀ = ϖ⁰ • A₀` is a neighbourhood, so `ϖᴺ r ∈ A₀` for some
  `N` — no `hϖ`. Discharge: `hbasis.mem_of_mem`, `(continuous_mul_right r).tendsto 0`. SURVIVED.
- **L11.2** `gaugeNorm_le_zpow_iff` — **the workhorse**: `N r ≤ a^{−n} ↔ r ∈ ϖⁿ • A₀`. Verified
  case by case in both directions, including `r ∈ ⋂` (`N r = 0`, both sides true) — so **no `T2`**.
  Discharge: `csInf_le`; `Int.exists_greatest_of_bdd`; `zpow_le_zpow_iff_right₀`. [2] `n < 0` ✓.
  SURVIVED.
- **L11.3** `gaugeNorm_eq_zero_or_exists_zpow`, `gaugeNorm_le_one_iff` — values in `{0} ∪ a^ℤ`
  (needed by L11.4 without `T2`); unit ball `= A₀` is L11.2 at `n = 0` ([JN] *"with unit ball
  `R₀`"*). SURVIVED.
- **L11.4** `gaugeNorm_add_le_max`, `gaugeNorm_neg`, `gaugeNorm_mul_le`, `gaugeNorm_unit_mul` —
  [JN] Def 2.1.1 (`jn.txt:476`): *"(2) `|r + s| ≤ max(|r|, |s|)`; (3) `|rs| ≤ |r||s|`"*, and
  *"`ϖ` is a multiplicative pseudo-uniformizer"*. Via L11.2–L11.3: `ϖⁿ A₀` is an additive
  subgroup; `ϖⁿ A₀ · ϖᵐ A₀ ⊆ ϖⁿ⁺ᵐ A₀`; `E(ϖ r) = E(r) + 1`. [2] `N r = 0`, `N s ≠ 0`:
  `r s ∈ ⋂` ✓. SURVIVED.
- **L11.5** `hasBasis_nhds_zero_gaugeNorm` — [RM] §0.4.6 *"inducing the topology of `A`"*.
  `{N < a^{−(n−1)}} = {N ≤ a^{−n}} = ϖⁿ • A₀` (values discrete, L11.3). SURVIVED.
- **L11.6** `gaugeNorm_eq_zero_iff`, `exists_gaugeNorm_eq_zpow`, `gaugeNorm_one`, `gaugeNorm_unit`,
  `gaugeRingNorm` — [RM] §0.4.6 *"⚠ The Hausdorff hypothesis is necessary: without it the formula
  gives only a seminorm, with kernel the closure of `0`"*. `T2`: `⋂ ϖⁿ A₀ = {0}`. `N 1 = 1`:
  `1 ∈ A₀`; `1 ∈ ϖ A₀` would give `ϖ A₀ = A₀`, all basis sets equal, `A₀ = {0}` by `T2`,
  contradicting `Nontrivial`. [3] `T2` and `Nontrivial` both necessary, as shown. [4] [JN] omit
  "Hausdorff" because their Tate rings are complete. SURVIVED.

---

## Examples (`Examples.lean`)

- **L12.1** `unitClosedBall_padic` — [RM] Examples *"`ℚ_p` … with `R⁰`"*. `Subring.ext`;
  `PadicInt.subring` has carrier `{x | ‖x‖ ≤ 1}`. SURVIVED.
- **L12.2** `ideal_padic_eq_openUnitBallIdeal` — L9.3 with `Padic.norm_eq_zpow_neg_valuation`,
  `Padic.norm_p` (`‖x‖ = p^{−v} = ‖p‖^{v}`). SURVIVED.
- **L12.3** `nonempty_residueRing_padic_equiv_zmod` — `PadicInt.toZMod` along the identity
  `unitClosedBall ℚ_[p] ≃+* ℤ_[p]`; `PadicInt.ker_toZMod`, `ZMod.ringHom_surjective`,
  `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotEquivOfEq`. SURVIVED.
- **L12.4** `norm_zpow_mul_mem_Ioc_iff` — [RM] Examples *"the shells … in `ℚ_p`"*. Computed:
  `‖pⁿ x‖ = p^{−(n+v)} ∈ (p⁻¹, 1] ↔ n + v = 0`. SURVIVED.
- **L12.5** `not_isTate_padicInt`, `norm_tsum_pow_padicInt`, `norm_tsum_pow_padicInt_sub_one` —
  [RM] §0.4.7 *"A non-example: `ℤ_[p]`, whose norm has no unit of norm less than `1`"*
  (`PadicInt.isUnit_iff`); acceptance example *"`‖∑' n, pⁿ‖ = 1` in `ℤ_p`"* (L2.10, L2.11,
  `PadicInt.norm_p`). SURVIVED.
- **L12.6** `exists_norm_p_lt_norm_lt_one_padicComplex`, `exists_zpowCeil_norm_ne_padicComplex`,
  `ideal_padicComplex_ne_openUnitBallIdeal` — [RM] Examples *"the rescaled norm on `ℂ_p` … is not
  the original norm"*. `x² = p` (`IsAlgClosed.exists_pow_nat_eq`), `‖x‖² = p⁻¹`,
  `PadicComplex.norm_extends`, `norm_algebraMap'`. SURVIVED.
- **L12.7** `isPowerBounded_int`, `norm_two_int`, `not_neBot_nhdsNE_zero_int` — [RM] §0.2.2 first
  counterexample. `V := {0}` is a neighbourhood in the discrete topology. SURVIVED.
- **L12.8** `L1Pair` (norm fields), `norm_mul_le`, `oneSubTwoX_sq`, `norm_oneSubTwoX`,
  `isPowerBounded_oneSubTwoX` — [RM] §0.2.2 second counterexample. Verified by hand:
  `(u,v)(u',v') = (uu', vv')`, `|uu'| + |vv' − uu'| = |aa'| + |ab' + ba' + bb'| ≤ (|a|+|b|)(|a'|+|b'|)`;
  `(1,−1)² = (1,1) = 1`; `‖(1,−1)‖ = 1 + 2 = 3`; powers in `{1, (1,−1)}`, so L3.2 applies with
  `C = 3`. SURVIVED.
- **E4 (not on this board).** [RM] Examples *"the Tate normed ring `ℚ_p⟨X⟩`"* and §0.4.7's `R⟨X⟩`,
  `Λ^{>1/p}[1/T]` need the normed rings of §4.1 and §5.6.

---

## Gate (Step 5)

1. **Every leaf discharged**: from Mathlib (names verified by elaboration, two scratch files, 140
   names, 5 misses replaced: `Set.Finite.exists_maximal_wrt` → `Finset.exists_max_image`,
   `NormedRing.*_geometric_*` → root `summable_geometric_of_norm_lt_one` etc.,
   `Subring.module` → found by `inferInstance`, `Real.logb_zpow` → `Real.logb_rpow`,
   `IsUniformEmbedding.completeSpace_iff` → `completeSpace_congr`), or from earlier leaves of this
   tree. **No API gap** remains inside the board; the two seams (E6, E7) are external by design.
2. **The skeleton compiles**: `lake build …Examples …NormComparison` — 2 626 jobs, 0 errors, `sorry`
   warnings only (2026-09-18).
3. **Every leaf has a verbatim quote** ([RM] always; literature where the statement has a source)
   and a match note.
4. **Adversarial pass**: every leaf above carries ≥ 3 attack categories. Attacks that *succeeded*
   and changed the plan: E2 (L2.14), E3 (L8.5), E5 (L6.0), non-subadditivity (L8.2), and the
   removal of `hϖ` from absorption (L11.1); hypotheses pruned at L1.4, L3.2, L3.4, L7.1, L7.3–4.
5. **Prior-B2 log**: consulted; one defect-shape match, addressed (table at the top).
6. **The tree mirrors the sources**: [JN] §2.1's order (normed rings → Tate → modules → norm
   comparison), [Bel] §II.1.4's residue objects, [Sch] Prop 10.1's rescaling, [Wed] §5.3/§6.2 for
   the Huber side. No size estimates are given anywhere in this tree.
7. **Single conclusions**: no leaf has a top-level `∧`; [JN] 2.1.6 and 2.1.7 are split (L7.1–2,
   L7.4–5); `∃!` (L6.2–3) is a shared-witness statement and stays whole.

No leaf is REVIEW-PENDING.
