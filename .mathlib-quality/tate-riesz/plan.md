# Development Plan: `tate-riesz` — ring-level Riesz theory over the halo Tate ring

**BOARD PATH: `.mathlib-quality/tate-riesz/`** — named board; the default `.mathlib-quality/`
root belongs to the (completed) NewtonPolygons project and `lwx-halo/`, `jacobs-explog/`, …
are other projects' property.  Every `/beastmode` invocation for this project must name this
path.  Planned 2026-09-05 (Fable 5.1), from the proposal recorded in
`.mathlib-quality/lwx-halo/plan.md` §"Future board 2 — `tate-riesz`".

House rules inherited from the sibling boards: no duplicate code; every deletion/rename →
this board's `renames.jsonl`; B2 stops → this board's `b2_log.jsonl`; `lia` → `omega`;
never touch `PhD/PR'd/`, `PhD/LegacyCode/`, or `PhD/JacobsSlash/1_PadicAnalytic.lean`
(the `jacobs-explog` board's file); any exp/log need goes through the **general layer**
`PhD/LWX/PadicExpLog.lean` / `PhD/LWX/UnitsLog.lean` (the completed exp/log refactor), never
the `p = 3` Jacobs code.  Another agent may build concurrently — never kill a running
`lake build`.

## Sources

| Tag | Reference | Local text (line locators) |
|---|---|---|
| `[JN]` | Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*, arXiv:1604.07739v4, §§2.1–2.3 | `references/jn.txt` (pdf pp. 7–15 = lines 471–1000) |
| `[Bel]` | Bellaïche, *The Eigenbook*, draft Ch. II: §II.1.6–II.1.7 (pp. 61–63), §II.2 (pp. 64–71), §II.3.2 (pp. 72–74) | `references/bellaiche.txt` (lines 2155–3070) |
| `[Buz07]` | Buzzard, *Eigenvarieties*, §2 (pp. 4–20), §3 (pp. 20–25) | `references/buzzard.txt` (lines 128–885) |
| `[LWX]` | Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, arXiv:1412.2584v4: Lemma 3.15, Thm 3.16, Cor 3.18 (pp. 21–23), Thm 1.3 Step II (pp. 25–26), Rmk 3.25 (p. 28) | `references/lwx.txt` (lines 1591–1700, 1880–1960, 2112–2122) |
| `[Col97]` | Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997), Appendix A3–A4 | **not to hand** (paywalled); cited through [Buz07] §3 and [Bel] §II.2.4, which reproduce the needed statements |
| `[Ke09]` | Kedlaya, *Semistable reduction for overconvergent F-isocrystals III*, Compos. Math. 145 (2009), Prop. 3.2.2 | fetched from arXiv math/0609645 (statement + opening of proof quoted in `decomposition.md`) |
| `[Serre]` | Serre, IHÉS 12 (1962), §7 Prop. 12 | already formalised: `PhD/TateFredholm/Riesz.lean` |

**Source-faithfulness map.** [JN] Thm 2.2.2's proof is one sentence: "Apart from the last
sentence, this is (a minor reformulation of) [Buz07, Theorem 3.3]" — so the substrate is
Buzzard's §3, whose Thm 3.3 in turn "follow[s] Theorem A4.3 of [10]" (Coleman).  Coleman's
appendix is not to hand; **Bellaïche's §II.2 reproduces the whole route with full proofs**
(II.2.8 Euclidean division, II.2.13–II.2.16 resultant theory and spectral mapping, II.2.17
Serre's projector, II.2.18 the theorem), and is the primary quoted source for the core.
Buzzard's Prop 3.2 / Thm 3.3 supply the refinements ([JN]'s rank, `Q*(u) = 0` on the kernel,
determinant identities) and Lemma 3.1, whose proof (Coleman A4.1) is reconstructed from
Bellaïche's identities + Serre's Prop 11 — the one place where the plan expands a source
that only cites a proof elsewhere (flagged in `decomposition.md` D4).

## Goal

Four deliverables (the proposal's four items), each a milestone-free tranche except the last:

1. **The Banach–Tate ring `A = HaloInt[1/T]`** (`PhD/LWX/HaloTate.lean`): `HaloTate p`, the
   localisation of `Λ^{>1/p}` at `T` realised as coefficient streams `d : ℤ → ℤ_[p]` with
   `‖d j‖ ≤ p^{min(0, j+k)}` for some `k`; gauge norm; `T` a unit with `‖T x‖ = p⁻¹‖x‖`, hence a
   multiplicative pseudo-uniformizer ([JN] Def 2.1.2) and `IsTate (HaloTate p)`; unit ball
   `= HaloInt p`.  **No Noetherian claim** (none is needed downstream; the sources' proofs
   never use it — see "Generality decisions").
2. **[JN] Theorem 2.2.2** (`PhD/TateFredholm/{Entire,Resultant,Coleman,RieszColeman}.lean`),
   over an arbitrary Banach–Tate ring and the model space `c(I, R)` with a compactoid `u`:
   for `det(1 − Tu) = Q·S`, `Q` multiplicative, `(Q, S) = R{{T}}`: a projector `p` in the
   closure of `R[u]` with `N := range (1 − p)` finitely generated projective of rank `deg Q`,
   `N = Ker Q*(u)`, `Q*(u)` invertible on the unique closed `u`-stable complement `range p`,
   `det(1 − Tu | N) = Q`, `det(1 − Tu | range p) = S`, `u` invertible on `N`.  Plus
   [Buz07] Lemma 3.1 in both directions.
3. **[JN] Theorem 2.2.13 at the norm level** (`PhD/TateFredholm/SlopeFactor.lean` +
   `RieszColeman.lean` §Refinements): the vertex/slope factorisation `F = P·G` of an entire
   series at a dominant index ([Bel] Thm II.3.6 existence — the "standard factorization
   argument [Ke09, 3.2.2]" of [LWX] Rmk 3.25), relative primality of its factors (norm-level
   [JN] Lemma 2.2.7, via Weierstrass division), and the decomposition core "for every
   multiplicative `P'` relatively prime to `S`, `P'*(u)` is invertible on `range p`".
4. **The application** (`PhD/LWX/TateRiesz.lean`): the `T`-rescaled *transpose* `V` of the
   integral `U_p` is a compactoid operator on `c(ι × ℕ, A)` with `det(1 − TV) = Char(P)`
   ([LWX] (3.16.1) read in `A⟦X⟧`); at a hypothesised vertex `c_n = T^{λ(n)}·(unit)`
   ([LWX] Rmk 3.25's `n^±_k`), `Char(P)` factors with a degree-`n` factor and JN 2.2.2 gives
   the Riesz decomposition of `c(ι × ℕ, A)` for `V` — **the milestone**.

**Out of scope (recorded so nobody re-litigates):** [JN] Def 2.2.4's slopes via the Gelfand
spectrum `M(R)` and residue fields `K_x` (mathlib has no Berkovich spectrum; the boundary
point of characteristic `p` with residue field `𝔽_p((T))` makes even the halo case
non-trivial), hence [JN] Lemma 2.2.7, Def 2.2.8–Prop 2.2.11 and Thm 2.2.13 *as stated*;
functoriality under `R → K_x` (completed tensor products); [JN] §2.3 spectral varieties (adic
spaces); the derivation of the vertex hypothesis `c_{n^±_k} = T^{λ}·unit` ([LWX] Thm 1.3's
touching argument: classicality + Atkin–Lehner); the infinite product
`P₀·P₍₀,₁₎·P₁·⋯` and the *integrality* of its factors (needs the successive-vertex
compatibility, i.e. uniqueness of dominant factorisations, which [Bel] proves only
pointwise); Noetherianity of `A`; `p = 2`; identifying `V` with the `U_p`-action on a
distribution/dual model (the halo board's H4 note: the rescaled basis is not `c₀`-stable,
so the transpose is the honest compact operator — the seam is recorded, not crossed).

## Mathematical route (per tranche)

* **B (entire series).** `IsEntire f := ∀ c > 0, IsRestricted c f` ([Bel] Def II.1.16), the
  subring `R{{T}}`; Euclidean division by a unit-leading polynomial ([Bel] Prop II.2.8) is
  Martin's Weierstrass division (`ForMathlib…MulWeierstrassDivision`) at a radius where the
  divisor is distinguished, with the quotient entire by uniqueness across radii (the pattern of
  `Riesz.lean`'s `exists_factor_of_evalT_eq_zero`); relative primality ([JN] Def 2.2.1) and
  [Bel] Cor II.2.9 in the form "`(B, F) = R{{T}}` iff `(B, F mod B) = 1` in `R[T]`"; good zeros
  ([Bel] Def II.2.11) with the Leibniz rule for `Δˢ` ([Buz07] p. 22) and [Bel] §II.2.3's
  factorisation; the identity theorem along `ϖᵏ` (supporting [Buz07] p. 20's product formula).
* **R (resultant).** `Res(charpoly A, g) = det g(A)`: over a domain where both split,
  `det g(A) = ∏ g(λᵢ)` by factoring `g` into linear factors and `det(A − μ) = ±charpoly A (μ)`;
  in general by `Matrix.charpoly.univ` (universal matrix and universal `g` over
  `ℤ[xᵢⱼ, yₖ]` ⊂ algebraic closure) and `resultant_map_map`.
* **C (Coleman's `D`).** `dPoly B P N := Res_X(reflect N P, 1 − T·B(X))` (mathlib
  `Polynomial.resultant`); [Bel] Lemma II.2.13 (i)–(iii) are `resultant_mul_left`,
  `resultant_add_mul_right/left` after `reflect_mul`; the unit criterion (Coleman A3.7) is
  mathlib's `isUnit_resultant_iff_isCoprime` for the monic `Q*` plus a reflection lemma; the
  finite spectral mapping is `Matrix.resultant_charpoly` + `reverse_charpoly`.  Analytic
  part: a crude Gauss-norm bound and a multilinearity (Lipschitz) estimate on the Sylvester
  determinant, Buzzard's renormalisation `D(B, P(λT)) = D(B(λX), P)`, `D(λB, P)(T) = D(B,P)(λT)`
  (unit `λ`, mathlib `resultant_scaleRoots`) giving the entireness estimate
  `‖coeff_j D‖ ≤ C^{deg B}(‖ϖ‖^m Cb)^j`; `dSeries B F` as the coefficientwise limit of
  `dPoly B (trunc F)` ([Bel] p. 68), multiplicative on entire series, and the key
  evaluation-at-`1` lemma `D(1 − Q̃*, S)(1)` unit `⟺ (Q, S) = R{{T}}` (division `S = Qq + r`,
  Martin's norm identity for continuity of `r`, dominated convergence of the evaluations);
  [Bel] Prop II.2.15; the operator spectral mapping [Bel] Prop II.2.16 by row truncation
  (`tendsto_truncation_comp`, `charCoeff_eq_det_coeff`, `norm_charCoeff_sub_le`).
* **D (Riesz–Coleman).** `φ' := aeval u (bQ Q v)` with `bQ Q v = 1 − v⁻¹ Q*`; its determinant
  `D(1 − Q̃*, QS)` has a good zero of order `deg Q` at `1`; `exists_rieszProjection` (Serre
  Prop 12, `Riesz.lean`) at `a = 1` gives `p, w`; strengthened by the "closure of `R[u]`"
  conjunct.  Finiteness of `N` by the Noetherian-free proof of [Bel] Prop II.1.21 run on the
  range of the idempotent; projectivity by the lifting property ([Bel] Prop II.1.20).
  Refinements per [Buz07] Prop 3.2/Thm 3.3: orthogonal multiplicativity
  `det(1 − T(v+w)) = det(1−Tv)det(1−Tw)` (from `fredholmDet_mul` at all `ϖᵏ` + identity
  theorem), polynomiality of `det(1 − Tu | N)`, Lemma 3.1, coprimality of `Q` with
  `det(1 − Tu | range p)`, hence `Q ∣ G`; rank `deg Q` at every prime by reduction modulo
  maximal ideals (`φ'` unipotent on `N ⊗ k(𝔪)` ⇒ `(1 − T)^{rank}` vs `(1 − T)^{deg Q}·(unit at 1)`),
  hence `deg G ≤ deg Q` by localisation, `G = Q`, Cayley–Hamilton ⇒ `Q*(u) = 0` on `N`,
  `S = det(1 − Tu | range p)` by cancelling the unit `Q` of `R⟦T⟧`, uniqueness by [Bel]'s
  nilpotent-and-invertible argument.
* **E (vertex factorisation).** [Bel] Thm II.3.6's Newton iteration (II.3.1)–(II.3.6) at the
  norm level: dominant index at radius `ρ`, dominant coefficient a multiplicative unit;
  Euclidean-division estimates (II.2.1) from Martin's `norm_eq_max_of_eq_mul_add_of_isMulDistinguished`.
  Coprimality of the factors by Weierstrass division at radius `ρ` (`G` is a unit of
  `R⟨ρ⁻¹T⟩`).
* **F (application).** `V := (D⁻¹PD)ᵀ` over `A` with entries `T^{n−m}·M_{(i,m),(j,n)}`; row
  bound `p^{−(n − ⌊n/p⌋)}` from the halo board's `UpDatum.norm_matrix_le`; minors invariant
  under transposition/diagonal conjugation ⇒ `det(1 − TV) = Char(P)` mapped along the
  isometry `HaloInt → A` (summability: `summable_minor_upOp`); at a vertex, dominant index
  `n` at `ρ = p^{λ(n) − λ(n−1)}` by convexity of `λ` (`lwxLambda_succ`, `monotone_sub_div`);
  then E2/E3 and D1.

## Mathlib / project inventory (verified at planning time)

| Concept | Status | Action |
|---|---|---|
| `Polynomial.resultant`, `resultant_mul_left/right`, `resultant_add_mul_left/right`, `resultant_C_mul_left/right`, `resultant_X_pow_left`, `resultant_succ_left_deg`, `resultant_add_right_deg`, `resultant_scaleRoots`, `resultant_map_map`, `resultant_eq_prod_eval`, `isUnit_resultant_iff_isCoprime` | `Mathlib/RingTheory/Polynomial/Resultant/Basic.lean` (verified by grep) | USE — Coleman's `D` and [Bel] II.2.13 |
| `Polynomial.reflect`, `reflect_mul`, `reflect_C_mul_X_pow`, `reflect_C`, `reflect_one`, `coeff_reflect`, `reverse`, `coeff_zero_reverse`, `reverse_leadingCoeff` | `Mathlib/Algebra/Polynomial/Reverse.lean` (verified) | USE — `Q*` |
| `Matrix.charpolyRev`, `reverse_charpoly`, `eval_charpolyRev`, `Matrix.charpoly.univ`, `univ_map_eval₂Hom`, `eval_charpoly`, `det_eq_prod_roots_charpoly_of_splits`, `isNilpotent_charpoly_sub_pow_of_isNilpotent` | Charpoly/{Coeff,Univ,Basic,Eigs}.lean (verified) | USE — R1, D6 |
| `Polynomial.Splits`, `Splits.eq_prod_roots`, `natDegree_eq_card_roots`, `IsAlgClosed` | Splits.lean / IsAlgClosed (verified) | USE — R1 |
| `Module.rankAtStalk`, `rankAtStalk_eq_finrank_tensorProduct`, `Module.free_of_flat_of_isLocalRing`, `Module.eq_zero_of_localization_maximal` | FreeLocus.lean, LocalRing/Module.lean, LocalProperties (verified) | USE — D6/D7 |
| `Submodule.IsTopCompl` API, `ContinuousLinearMap.IsIdempotentElem.isTopCompl` | Topology/Algebra/Module/Complement.lean (verified) | USE — D8 |
| `Polynomial.hasseDeriv_mul` (pattern) | Mathlib HasseDeriv.lean | MIRROR for `PowerSeries.hasseDeriv` (project def) |
| `PowerSeries.IsRestricted`, `Restricted R c`, Gauss norm, `weierstrassDivision_exists/…_q_unique/…_r_unique_of_isMulDistinguished`, `isMulDistinguished_toRestricted_of_monic`, `norm_eq_max_of_eq_mul_add_of_isMulDistinguished`, `norm_mul_of_isMulDistinguished` | `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/*` (verified) | USE — B2, E1, E2, E3 |
| `Polynomial.gaussNorm`, `gaussNorm_mul_le` | `PhD/ForMathlib/RingTheory/Polynomial/GaussNorm.lean` (verified) | USE — C3 |
| `PowerSeries.evalT`, `evalT_add/mul`, `hasseDeriv`, `isRestricted_hasseDeriv` (private), `exists_rieszProjection`, `ker/range_one_sub_smul_pow_of_rieszProjection`, `isTopCompl_range_one_sub_range_of_isIdempotent`, `rieszProjection_unique`, `isUnit_one_sub_smul_iff_isUnit_evalT`, `fredholmDet_mul`, `charCoeff_smul`, `resolventPartialSum`, `IsOpLimit` API | `PhD/TateFredholm/Riesz.lean` (verified) | USE — D1, D3, D4; one strengthening (D1: `IsOpLimit` conjunct) |
| `finite_projective_of_one_sub_compact_nilpotent`, `HasPr.projective`, `exists_lift_cSpace` (private) | `PhD/TateFredholm/Pr.lean` (verified) | MIRROR on the range of an idempotent (D2); refactor to expose the lifting lemma; drop the unused `[IsNoetherianRing R]` |
| `charPowerSeries_comm/conj/extendZero`, `charCoeff_eq_det_coeff`, `norm_charCoeff_sub_le`, `charPowerSeries_isEntire`, `tendsto_truncation_comp`, `IsCompactoid.add/smul/comp_right` | Fredholm/Matrix/Riesz (verified) | USE — C6, D3 |
| `HaloInt` ring/norm construction, `tendsto_cofinite_of_three_bounds` (private), `norm_T_mul`, `exists_T_pow_mul_of_norm_le` | `PhD/LWX/HaloRing.lean` (verified) | MIRROR with shifted bounds (A1–A3); un-private the summability workhorse |
| `UpDatum.op/matrix`, `norm_matrix_le`, `matrixCoeff_op`, `summable_minor_upOp`, `norm_charCoeff_upOp_le`, `lwxLambda(_succ)`, `monotone_sub_div` | `PhD/LWX/{UpMatrix,Halo}.lean` (verified) | USE — F1–F3 |
| Gelfand spectrum / Berkovich points | NOT in mathlib | OUT OF SCOPE (slopes reformulated at the norm level) |
| `Res(charpoly A, g) = det g(A)` | NOT in mathlib | DEFINE (R1) — PR candidate |
| entire series ring `R{{T}}`, Euclidean division in it, Coleman's `D` | NOT in mathlib, not in project | DEFINE (B, C) |

## File structure (all new files; edits to existing files are limited to the three refactors named below)

```
PhD/TateFredholm/Entire.lean       — IsEntire, entireSubring, Euclidean division, IsEntireCoprime,
                                     Cor II.2.9, IsGoodZero + factorisation, Leibniz, identity theorem
PhD/TateFredholm/Resultant.lean    — Res(charpoly A, g) = det g(A)   (mathlib-only imports)
PhD/TateFredholm/Coleman.lean      — gPoly/dPoly/bQ, [Bel] II.2.13, unit criterion, Matrix.charpolyRev_aeval,
                                     estimates, dSeries, II.2.14/II.2.15, spectral mapping II.2.16
PhD/TateFredholm/RieszColeman.lean — exists_rieszColemanProjection (JN 2.2.2 core), closure-of-R[u],
                                     restriction/finiteness/projectivity, orthogonal multiplicativity,
                                     Lemma 3.1, IsRieszColemanProjection refinements, uniqueness, 2.2.13-core
PhD/TateFredholm/SlopeFactor.lean  — IsDominantIndex/Poly, [Bel] II.3.6 existence, norm-level Lemma 2.2.7
PhD/LWX/HaloTate.lean              — the Tate ring A
PhD/LWX/TateRiesz.lean             — tateOp, compactoidness, Char(P), IsHaloVertex, Rmk 3.25 core, milestone
```
Existing-file edits (each its own ticket line, recorded in `renames.jsonl` if a name moves):
(i) `Riesz.lean`: un-private nothing; D1 adds a *new* theorem `exists_rieszProjection_isOpLimit`
in RieszColeman.lean (no edit needed unless the worker prefers to strengthen in place);
(ii) `Pr.lean`: expose `exists_lift_cSpace` (D2) and drop the unused `[IsNoetherianRing R]` from
`finite_projective_of_one_sub_compact_nilpotent` (README claim to be updated);
(iii) `HaloRing.lean`: un-private `tendsto_cofinite_of_three_bounds` (A1).

Import spine: Riesz ← Entire ← {Coleman (← Resultant), SlopeFactor} ; Coleman + Pr ← RieszColeman ;
HaloRing ← HaloTate ; {HaloTate, Halo, RieszColeman, SlopeFactor} ← TateRiesz.
`lake build` of the skeleton: **2898 jobs, sorries only** (verified 2026-09-05).

## Dependency graph (tranche level)

```
A1 → A2 → A3 → CLEANUP-A ─────────────────────────────────────────┐
B1 → B2 → B3 → CLEANUP-B1 → B4 → CLEANUP-B2 ──────────┐          │
R1 → CLEANUP-R ──────────┐                            │          │
C1 ──┬→ C2 (needs R1) ───┼→ C5 ─┐                     │          │
     └→ C3 → CLEANUP-C1 → C4 ───┼→ C6 → CLEANUP-C2 ───┼──┐       │
D2 (Pr.lean, independent) ──────┼───────────────────── │  │       │
D3 (needs B4) ──────────────────┼───┐                  │  │       │
                                └───┴→ D1 → D4 → D5 → D6 → CLEANUP-D2 → D7 → D8 → CLEANUP-D3
       (CLEANUP-D1 after D3)                                                        │
E1 (needs B1) → E2 (needs B2) → E3 (needs B3) → CLEANUP-E ──────────────────────────┤
F1 (needs A3) → F2 → F3 (needs E1) → CLEANUP-F1 ──────────────────────────────────┤
all of the above → CLEANUP-ALL-1 → F4 (milestone) → CLEANUP-F2 → CLEANUP-FINAL
```
Parallel capacity at start: A1 ∥ B1 ∥ R1 ∥ C1 ∥ D2 (5 workers).

## Generality decisions

- **No Noetherian hypothesis anywhere.** [JN] state 2.2.2/2.2.13 for Noetherian `R`; the
  proofs ([Buz07] §3, [Bel] §II.2) use Noetherianity only through [Buz07] Lemma 2.3 (closedness
  of f.g. submodules — bypassed by the `IsCompactoid` hypothesis, as everywhere in
  `TateFredholm`) and [Bel] Prop II.1.21 (whose proof does not use it — recorded in
  `Pr.lean`).  Every theorem of this board therefore strictly generalises its [JN] statement,
  and `A` needs no Noetherianity proof.
- **Model space, not (Pr) modules.** Statements are for `c(I, R)` and compactoid `u`; transport
  to (potentially) ON-able modules is `charPowerSeries_conj`; (Pr) modules via
  `charPowerSeries_extendZero` is a follow-up (no consumer on this board).
- **Slopes at the norm level.** "Slope `≤ h`" ↦ "`ρ`-dominant polynomial" and "slope `> h`" ↦
  "dominant index `0` at radius `ρ`" (`ρ = |ϖ|^{-h}`); over a field these are [Bel] Lemma
  II.2.7's Newton-polygon conditions.  Relative primality of the factors is then a
  Weierstrass-division statement, not a Gelfand-spectrum one.
- **`Q*` is `Polynomial.reverse`**, normalised with the explicit unit `v = leadingCoeff Q`
  passed as a parameter (`bQ Q v = 1 − v⁻¹ Q*`), so `Q*` stays monic and mathlib's
  `isUnit_resultant_iff_isCoprime` applies verbatim.
- **Rank as `Module.rankAtStalk` at every prime** (mathlib's notion), not a global
  "constant rank" predicate.
- **The application uses the transpose.** `V = (D⁻¹PD)ᵀ` is what is compactoid over `A`
  (prior-B2 log of `lwx-halo`, H4/H5: the rescaled coordinates are not `c₀`); its Fredholm
  determinant equals `Char(P)`, so [JN] 2.2.2 applies to it verbatim.
- Cleanup tickets: 13 (per-file cadence every 3 proof tickets + final per file + `CLEANUP-ALL`
  before the milestone + `CLEANUP-FINAL`).

## ChatGPT validation

Skipped: the `chatgpt-math` MCP server failed to connect this session (cached failure).
To be run at the user's discretion before execution if desired.

## Ratification record (2026-09-05, user review)

**All six decisions are ratified (2026-09-05).**  Decisions 3 (no Noetherian hypothesis — "this is
the point of using Bellaïche"), 4 (the transposed operator, provided facts about the true `U_p`
follow — see below) and 6 (exp/log only through `PhD/LWX/PadicExpLog.lean`) were ratified at the
first review; decision 1 ("do your suggested plan" — the recommended proofs below are the plan),
decision 2 (with the recovery note below) and decision 5 (the Atkin–Lehner chain below) at the
second.  **The board is approved for execution: run `/beastmode` naming
`.mathlib-quality/tate-riesz/`.**

### Decision 1 — recommended proofs

- **Core theorem ([JN] 2.2.2):** Bellaïche's route (Thm II.2.18), as planned.  It is the only
  route whose every input is either already formalised (`exists_rieszProjection`, Serre's
  Prop 12) or a mathlib resultant identity (Lemma II.2.13); Coleman's original goes through the
  same objects with less detail, and Buzzard only points at Coleman.
- **Refinements (rank `deg Q`, `Q*(u) = 0` on `N`, `det` identities):** Buzzard's Prop 3.2
  argument — reduction modulo maximal ideals, run for `φ' = 1 − Q*(u)/Q*(0)` at the linear
  factor `1 − T`, then transferred to `Q` via `Q ∣ G` — with the "`deg G ≤ deg Q`" step done by
  localisation at maximal ideals (`N_𝔪` free of rank `deg Q`).  Two shortcuts were tested at
  planning time and rejected: (i) "`det(1 − T·q) = (1 − T)^{deg Q}` for the idempotent `q`"
  fails over rings with idempotents of non-constant rank (`R = K × K`); (ii) chasing `D`-identities
  alone (`D(1 − Q̃*ᵐ, G)` for all `m`) cannot see the nilpotency of `Q*(u)` on `N` — a root `t` of
  `G*` with `Q̃*(t) = 1` is invisible to every `D(1 − Q̃*ᵐ, ·)`.
- **[Buz07] Lemma 3.1 (Coleman A4.1):** the four-equivalence proof
  `Q*(u)` unit ⟺ `1 − φ'` unit ⟺ `P_{φ'}(1)` unit (Serre 11) ⟺ `D(1 − Q̃*, P_u)(1)` unit
  (spectral mapping) ⟺ `(Q, P_u) = R{{T}}` (unit criterion).  Both directions come for free
  from the core's leaves; no separate resultant theory is needed.
- **Norm-level [JN] Lemma 2.2.7:** the Weierstrass-division proof (`G` is a unit of `R⟨ρ⁻¹T⟩`,
  so its remainder modulo `P` is a unit of `R[T]/(P)`); it avoids the Gelfand spectrum entirely.

### Decision 2 — what the scope cut means

[JN] Definition 2.2.4 defines "`F ∈ R⟦T⟧` has slope `≤ h`" pointwise: *for every* `x` in the
Gelfand (Berkovich) spectrum `M(R)` — the bounded multiplicative seminorms on `R` — the
specialisation `F_x` to the completed residue field `K_x` has all Newton-polygon slopes `≤ h`.
For `A = HaloInt[1/T]` the spectrum contains, besides the boundary Gauss norm of `A` itself,
points of characteristic `p`: `A/p ⊇ 𝔽_p((T))` with its `T`-adic norm is bounded by `‖·‖_A`
(it sends `p` to `0`), so the "extended" part of the eigenvariety over the boundary is exactly
what these points see.  [JN]'s Lemma 2.2.7 ("slope `≤ h` and slope `> h` ⇒ relatively prime")
is proved by specialising Coleman's resultant to every `x ∈ M(R)` and invoking Berkovich's
Corollary 1.2.4 (a series is a unit iff its coefficients are quasinilpotent at all points).
Mathlib has no Berkovich spectrum, no residue fields `K_x`, and no completed tensor products
`M ⊗̂_R K_x`, so Definitions 2.2.4/2.2.12 and Theorem 2.2.13 cannot even be *stated* faithfully.

What the board does instead: "slope `≤ h`" becomes "`ρ`-dominant polynomial" and "slope `> h`"
becomes "dominant index `0` at radius `ρ`" (`ρ = |ϖ|^{−h}`), both read at the single Gauss norm
of `R` ([Bel] Definitions II.2.3–II.2.4).  **Recovery note (user, 2026-09-05):** the lost
information — the pointwise slope conditions over `M(A)` including its characteristic-`p`
points, the converse of Theorem 2.2.13, functoriality under `R → K_x`, and §2.3's spectral
varieties — is exactly what a proper rigid/adic-space development would supply (Berkovich or
Huber spectra with residue fields and completed tensor products); it is deferred with that
pointer, not abandoned.  When such a development exists, the norm-level statements here are
the "generic point" specialisations of the pointwise ones and should be reusable as-is.  Over a field this *is* the Newton-polygon condition
([Bel] Lemma II.2.7), and over `A` it is the condition at the boundary point only.  What is
kept: the direction "factorisation ⟹ decomposition" of Theorem 2.2.13 (the one the
eigenvariety construction consumes), the relative primality of the factors, and everything
the halo application needs (Remark 3.25's factorisation at a vertex, the rank-`n` projective
slope piece).  What is lost: the converse direction, functoriality under `R → K_x`, the
characteristic-`p` points' slope conditions, and §2.3's spectral varieties (adic spaces).

### Decision 4 — what the transposed operator yields for the true `U_p`

The halo board's `UpDatum.op` (the plain-Mahler-basis `U_p` matrix `P`) is bounded on
`c(ι × ℕ, A)` but not compactoid: its row `m` contains entries of norm `1` for all `n ≥ pm`
(e.g. `P_{0,n} = binom(b/d, n)·[d]` is a unit for infinitely many `n`).  The `T`-rescaled matrix
`P' = D⁻¹PD` of [LWX, Thm 3.16] has uniformly decaying *columns*, i.e. its transpose `V` is
compactoid — the same phenomenon that produced the `lwx-halo` B2 entries (rescaled
coordinates are `ℓ^∞`, not `c₀`).  Morally `V` is `U_p` on the dual (distribution) model, which
is where [JN] themselves place their Riesz theory (their §3 works with `D(G, R)`).  Facts about
the true `U_p` that follow from this board without any further seam:

1. **The Fredholm determinant.** `det(1 − TV) = Char(P)`, the halo board's `charPowerSeries (D.op ω)`
   read in `A⟦X⟧` (transposition and diagonal conjugation preserve principal minors).  Every
   statement about `Char(P)` — the factorisation `Char = P_n·G` with `deg P_n = n` at a vertex
   (Remark 3.25), uniformly over the boundary annulus — is a statement about the true `U_p`'s
   characteristic series, hence about its slopes and eigenvalues at every specialisation
   (`Riesz.lean`'s field-level theory: zeros of `det(1 − Tu)` are reciprocal eigenvalues).
2. **The slope piece as an `A`-module.** `Ker P_n*(V)` is finitely generated projective of rank `n`
   over `A` with `det(1 − TV | Ker) = P_n`: the integral model of the slope-`≤` piece over the
   boundary annulus, on the dual side.  Its Hecke eigen-data are those of `U_p` (transposition
   preserves characteristic series and commuting families).
3. **At each point `T₀` of the annulus** the coefficientwise specialisation (`HaloInt.specialize`,
   `norm_specialize_le`) turns the factorisation into `Char(T₀) = P_n(T₀)·G(T₀)` with a
   Newton-polygon vertex at `n`; the field-level Riesz decomposition already in `Riesz.lean` then
   applies to the compact `U_p` at `T₀` once its model is identified.

Seams, recorded not crossed: (a) [LWX] Prop 2.17 — identifying `Char(P)` with the characteristic
series of `U_p` on the overconvergent space `S^{D,†}` (the halo board's "one remaining model
seam", needed for any statement about `S^{D,†}` rather than about the integral model);
(b) the identification of `V` with the `U_p`-action on a distribution/dual model.  Neither is
needed for items 1–3 above.

### Decision 5 — dependence on Atkin–Lehner and classicality (deferred, as planned)

The milestone F4 is **conditional** on `IsHaloVertex D ω n`: "`c_n = T^{λ(n)}·(unit of Λ^{>1/p})`
at a genuine vertex of `λ`".  In [LWX] this is *derived*, not assumed; the derivation is the
proof of Theorem 1.3, Steps I–II (`references/lwx.txt` 1807–1911), and it is exactly the
material the `lwx-halo` plan deferred to a future board.  The chain, with the statements the
future board must supply:

1. **[LWX] Prop 2.17** (`lwx.txt` 966–990): the integral model's `Char(P)` "agrees with the
   characteristic power series" of `U_p` on the overconvergent space `S^{D,†}` at each weight —
   so that Newton-polygon slopes of `Char(T_{χ_k})` are the `U_p`-slopes on `S^{D,†}_{(k,ψ)}`.
   (The halo board's recorded model seam; a Mahler ↔ analytic-basis change.)
2. **[LWX] Prop 3.22 (Atkin–Lehner)** (`lwx.txt` 1763–1770): "We use `α_0(ψ), …` to denote the
   slopes of `U_p` acting on `S^D_{k+2}(K^p Iw_{p^m}, ψ)` in non-decreasing order. Then we have
   `α_i(ψ) = k + 1 − α_{(k+1)q⁻¹p^m t − 1 − i}(ψ⁻¹)` … In particular, the total sum of the `U_p`-slopes
   of `S^D_{k+2}(…;ψ) ⊕ S^D_{k+2}(…;ψ⁻¹)` is `(k+1)²q⁻¹p^m t`."  Proved via Jacquet–Langlands and the
   local structure of the `p`-component (principal series), i.e. genuinely automorphic input.
3. **[LWX] Prop 2.15 (classicality, [Bu04, Prop 4])** (`lwx.txt` 913–920): for a `U_p`-eigenvector
   `ϕ ∈ S^{D,†}_χ` with eigenvalue `λ`, "If `v(λ) < k + 1`, then `ϕ` is classical".  Hence "the set
   of all `U_p`-slopes on `S^D_{k+2}(…;ψ) ⊕ S^D_{k+2}(…;ψ⁻¹)` is exactly the set of the first
   `n_{k+1}` `U_p`-slopes in each of `S^{D,†}_{(k,ψ)}` and `S^{D,†}_{(k,ψ⁻¹)}`" (Step I).
4. **The touching computation (3.23.1)** (`lwx.txt` 1852–1872): the lower-bound polygon of
   Corollary 3.18 at `x = (k+1)qt = n_{k+1}` has height `(k+1)²qt/2`, "This exactly agrees (!) with
   half of the sum of the first `n_{k+1}` `U_p`-slopes … That is, the Newton polygon of
   `∑ c_n(T_{χ_k})Xⁿ` passes through the point `(n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`."  (The `λ`-sum
   identity is elementary floor arithmetic — provable on this board's tools — but the touching
   needs 2 + 3.)
5. **Step II** (`lwx.txt` 1880–1911): the segment of the Newton polygon through that point has
   endpoints `n^−_{k+1} ∈ [n_{k+1} − t, n_{k+1}]`, `n^+_{k+1} ∈ [n_{k+1}, n_{k+1} + t]`, "the minimal
   index … (resp. maximal index …) such that `b_{n^∓_{k+1}, λ(n^∓_{k+1})}` is a `p`-adic unit in
   `ℤ_p`" — by Corollary 3.18's equality case (3.23.2): `v(c_n(T)) = λ(n)v(T)` iff `b_{n,λ(n)} ∈ ℤ_p^×`.
   These `n^±_k` are vertices of `λ`'s polygon (Step II's convexity statement).
6. **Bridge to `IsHaloVertex`** (this board, ticket F3b): `b_{n,λ(n)} ∈ ℤ_p^×` together with
   `c_n ∈ T^{λ(n)}Λ^{>1/p}` (Theorem 3.16, `exists_charCoeff_upOp_eq_T_pow_mul`) gives
   `c_n = T^{λ(n)}·e` with `e ∈ Λ^{>1/p}` of unit constant coefficient, hence a unit
   (`HaloInt.isUnit_of_isUnit_coeff_zero`) — `UpDatum.isHaloVertex_of_isUnit_coeff` is the exact
   interface the future board plugs into.

So the future Atkin–Lehner/classicality board owes this board precisely:
`∀ k, IsUnit ((charCoeff (D.op ω) n^±_k) (lwxLambda … n^±_k))` for the indices `n^±_k` of Step II,
together with the vertex condition on `λ` at those indices.

**Post-execution note (2026-09-06, after F4/F3b).**  That last clause is not automatic, and it is
the one open seam between this board and [LWX] Remark 3.25.  `λ`'s increments are
`d_n = ⌊n/t⌋ − ⌊n/(pt)⌋`, so `d_n − d_{n−1} = [t ∣ n] − [pt ∣ n]`: **`λ` has a genuine vertex
exactly at the multiples of `t` that are not multiples of `pt`** (checked for several `(p, t)`).
In particular `λ` has NO vertex at the touching abscissae `n_k = kpt` themselves, and the unit
indices `n^±_k ∈ [n_k − t, n_k + t]` of Step II are vertices of `λ` only when they fall on
`n_k ∓ t`.  Consequently `IsHaloVertex` as formalised covers the case "the touching happens at a
corner of `λ`", which is what gives dominance at the radius `p^{λ(n)−λ(n−1)}` from the halo bound
alone; for a general `n^±_k` sitting inside a segment of `λ`, dominance still holds but its proof
needs the *strictness off the unit indices* (the margin of `PhD/LWX/Sharpness.lean`, i.e. `c_m` is
strictly below the `λ` bound when `b_{m,λ(m)}` is not a unit), lifted from a single specialisation
to the `A`-norm.  Nothing in `SlopeFactor.lean` or `RieszColeman.lean` needs changing for that:
`exists_isDominantFactorization` consumes an arbitrary `PowerSeries.IsDominantIndex ρ F n`, so the
follow-up board only has to produce that predicate at `n^±_k` and then iterate the factorisation to
get Remark 3.25's product `P₀·P₍₀,₁₎·P₁·⋯`.  Everything below that hypothesis
(the factorisation of `Char(P)`, the rank-`n` projective slope piece) is unconditional here.
The `lwx-halo` plan lists the same inputs (Prop 3.22, Prop 2.15, Prop 2.17, Hida 3.19/3.21) as
"still deferred with no board"; they enter this board only through `IsHaloVertex`.
