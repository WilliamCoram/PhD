# Ticket Board — `tate-riesz` (ring-level Riesz theory over the halo Tate ring)

**BOARD PATH: `.mathlib-quality/tate-riesz/`** — name it in every invocation.  Other boards
(`lwx-halo/`, `jacobs-explog/`, `jacobs/`, `qmf/`, root NewtonPolygons, …) are other projects'
property — never touch them.  Read `plan.md` and `decomposition.md` (this directory) first:
every ticket below is "fill the sorries at file:lines" against the compiled skeleton
(`lake build` 2898 jobs, sorries only, 2026-09-05); the source quotes, Lean ↔ source
paragraphs and attack logs per leaf live in `decomposition.md` (labels `L-A1`, …).

House rules: no duplicate code; every deletion/rename → this board's `renames.jsonl`; B2 stops →
this board's `b2_log.jsonl`; `lia` → `omega`; never touch `PhD/PR'd/`, `PhD/LegacyCode/`,
`PhD/JacobsSlash/1_PadicAnalytic.lean`; exp/log needs (none expected) go through
`PhD/LWX/PadicExpLog.lean`/`UnitsLog.lean`; another agent may build concurrently — never kill a
running `lake build`.  Statement changes are B2 territory (record; ask).

## Summary
- Total: 47 tickets (34 proof/definition + 13 cleanup)
- Open: 0 | In Progress: 0 | Done: 47 — **BOARD COMPLETE 2026-09-06**
- **Conditional milestone:** F4 assumes `IsHaloVertex` (Atkin–Lehner + classicality input,
  deferred by design — see plan.md "Decision 5" for the exact chain and the interface F3b provides)
- Parallel capacity at start: 5 (A1 ∥ B1 ∥ R1 ∥ C1 ∥ D2)

## Dependency fronts
```
A1 → A2 → A3 → CLEANUP-A
B1 → B2 → B3 → CLEANUP-B1 → B4 → CLEANUP-B2
R1 → CLEANUP-R
C1 → C2 (needs R1) ; C1 → C3 → CLEANUP-C1 → C4 (needs B1) → C5 (needs C2, B2, B3) → C6 → CLEANUP-C2
D2 (Pr.lean, independent) ; D3 (needs B4) → CLEANUP-D1
D1 (needs C5, C6) → D4 (needs C5, C6, B3) → D5 (needs D1–D4) → D6 → CLEANUP-D2 → D7 (needs B2) → D8 → CLEANUP-D3
E1 (needs B1) → E2 (needs B2) → E3 (needs B3) → CLEANUP-E
F1 (needs A3) → F2 → F3 (needs E1) → CLEANUP-F1 → F3b
everything → CLEANUP-ALL-1 → F4 (milestone; needs F3b) → CLEANUP-F2 → CLEANUP-FINAL
```

---

## Tranche A — the Tate ring `A = HaloInt[1/T]` (`PhD/LWX/HaloTate.lean`)

### [A1] Carrier, convolution, ring structure, `ofInt`
- **Status**: done (finished 2026-09-05T12:25Z) | **File**: PhD/LWX/HaloTate.lean (+ one un-private in PhD/LWX/HaloRing.lean)
  | **Depends on**: none | **Parallel**: yes | **Type**: def + lemma
- **Statement**: fill the sorries in `norm_coeff_le_one` (:55), `ofInt_injective` (:64),
  `summable_mul_coeff` (:69), the bound fields of the `Zero/One/Add/Neg/Mul` instances (:73–81),
  the `CommRing` proof fields (:95–110), `coeff_sub` (:112), `ofIntRingHom` fields (:116–121).
- **Progress**:
  - 2026-09-05T12:25Z: DONE — all A1 sorries filled exactly per sketch (shifted three-bounds
    lemma, `HaloInt.tendsto_cofinite_of_three_bounds` un-privated + recorded in renames.jsonl;
    `norm_coeff_le_one` is `PadicInt.norm_le_one`; `ofIntRingHom` fields are `rfl`).  `lake build`
    clean, axioms standard.  Phase 6.5: file-level /cleanup deferred to CLEANUP-A per the board's
    cadence (A2/A3 edit the same file next), as on the lwx-halo board.
- **Proof sketch** (mirror of HaloRing.lean A1, decomposition L-A1):
  1. Un-private `tendsto_cofinite_of_three_bounds` in HaloRing.lean (record in `renames.jsonl`);
     `summable_mul_coeff`: with bounds `k₁, k₂` from `exists_bound`, apply it with
     `a i = i + k₁`, `b i = k − i + k₂`, `c = 0` (finiteness: `{i | −N ≤ i + k₁ ∧ −N ≤ k − i + k₂}`
     is an interval) then `summable_of_tendsto_cofinite`.
  2. Bound fields: `Zero/One` with `k = 0`; `Add/Neg` with `k = max k₁ k₂` and the ultrametric
     `norm_add_le_max`; `Mul` with `k = k₁ + k₂` (each term `‖f_i g_{k−i}‖ ≤ p^{min(0,i+k₁)+min(0,k−i+k₂)} ≤
     p^{min(0, k + k₁ + k₂)}`, then `norm_tsum_le_iSup`).
  3. `CommRing`: `mul_assoc` exactly as HaloRing (tsum_mul_left/right, `Summable.tsum_prod'`,
     the shear equivalence; the per-fibre summability from step 1), `mul_comm` via `Equiv.subLeft`,
     distributivity via `tsum_add`, `one_mul/mul_one` via `tsum_eq_single`.
  4. `ofIntRingHom`: coefficientwise `rfl` for `+`, `1`, `0`; `map_mul'` is the same tsum.
- **Mathlib lemmas needed**: `Summable.tsum_prod'`, `tsum_mul_left/right`, `tsum_add`,
  `tsum_eq_single`, `Equiv.subLeft`, `Equiv.tsum_eq`, `IsUltrametricDist.norm_add_le_max`,
  `TateFredholm.summable_of_tendsto_cofinite`, `TateFredholm.norm_tsum_le_iSup`.
- **Sources**: [LWX] Lemma 3.15, Cor 3.18 proof (`references/lwx.txt` 1591–1595, 1689–1690);
  HaloRing.lean:44–262.
- **Generality**: odd `p` not needed here; `k` existential (no canonical `k`).

### [A2] Gauge norm, completeness, unit ball
- **Status**: done (finished 2026-09-05T12:40Z) | **File**: PhD/LWX/HaloTate.lean | **Depends on**: A1 | **Parallel**: no
  | **Type**: instance + lemma
- **Statement**: `gaugeNorm` fields (:128–133), `bddAbove_range_norm_coeff` (:139),
  `norm_coeff_le_norm` (:143), `NormedRing.norm_mul_le` (:149), `NormOneClass` (:151),
  `IsUltrametricDist` (:154), `CompleteSpace` (:158), `norm_ofInt` (:165), `norm_le_one_iff` (:170).
- **Progress**:
  - 2026-09-05T12:40Z: DONE — mirror of HaloRing's norm section with the shifted term bound
    `gterm_le_of_bound` (≤ p^k); completeness uses `cauchySeq_bdd` + `pow_unbounded_of_one_lt`
    for the uniform shift `K` and `coeff_bound_of_norm_le`; `norm_ofInt` is `rfl`; added the
    public `norm_coeff_le_norm_mul` (‖f i‖ ≤ ‖f‖ p^i). Build clean, axioms standard. Cleanup
    deferred to CLEANUP-A.
- **Proof sketch** (L-A2; mirror HaloRing.lean:265–440):
  1. `bddAbove`: `‖f j‖p^{−j} ≤ p^{min(0,j+k)−j} ≤ p^k`.  All `gnorm_*` lemmas transfer with
     `ciSup_le`/`le_ciSup` against this bound.
  2. `norm_mul_le`: termwise `‖f_i g_{k−i}‖p^{−k} ≤ (‖f_i‖p^{−i})(‖g_{k−i}‖p^{−(k−i)})` + `norm_tsum_le_iSup`.
  3. `CompleteSpace`: a Cauchy sequence is bounded, `‖u_n‖ ≤ p^K`, hence `‖u_n j‖ ≤ p^{min(0,j+K)}`
     uniformly (from `norm_coeff_le_norm` and `norm_coeff_le_one`); coefficientwise Cauchy via the
     `p^j`-Lipschitz coefficient maps; the limit stream has the same bound `K`; convergence as in
     HaloRing.lean:392–435.
  4. `norm_le_one_iff`: `(⇐)` is `norm_ofInt` + `HaloInt.norm_le_one`; `(⇒)` `‖f‖ ≤ 1 ⇒ ‖f j‖ ≤ p^j`
     and `‖f j‖ ≤ 1` ⇒ `HaloInt` bound; the witness is `⟨f, _⟩`.
- **Mathlib lemmas needed**: `ciSup_le`, `le_ciSup`, `Real.iSup_le`, `Metric.complete_of_cauchySeq_tendsto`,
  `cauchySeq_tendsto_of_complete`, `LipschitzWith.uniformContinuous`, `Metric.cauchySeq_iff`.
- **Sources**: [JN] Rmk 2.1.3(1) (`jn.txt` 495–500); HaloRing.lean norm section.
- **Generality**: as HaloRing.

### [A3] `T` as a multiplicative pseudo-uniformizer; `IsTate A`
- **Status**: done (finished 2026-09-05T12:55Z) | **File**: PhD/LWX/HaloTate.lean | **Depends on**: A2 | **Parallel**: no
  | **Type**: def + lemma
- **Statement**: `T` fields (:176–180), `coeff_T_mul` (:185), `norm_T_mul` (:190), `norm_T` (:194),
  `norm_T_lt_one` (:197), `exists_T_zpow_mul_ofInt` (:214), `isMultiplicative_ofInt_of_isUnit`
  (:220), `isMultiplicative_mul` (:225; after CLEANUP-A this is `TateFredholm.IsMultiplicative.mul` in Tate.lean).
- **Progress**:
  - 2026-09-05T12:55Z: DONE — `T` as a unit (private `Tinv = δ₋₁`, `tsum_eq_single` both ways),
    `coeff_T_mul`/`coeff_T_pow_mul`, `norm_T_mul` (mirror), `norm_T`, `IsTate` instance,
    `exists_T_zpow_mul_ofInt` via `coeff_T_pow_mul` + `Units` power cancellation, the two
    multiplicativity lemmas. HaloTate.lean sorry-free (0), axioms standard, build clean.
- **Proof sketch** (L-A3): `val_inv/inv_val` by `tsum_eq_single`; `coeff_T_mul` as HaloRing
  `coeff_T_mul`; `norm_T_mul` as HaloRing:473–495 (two `ciSup` inequalities with the shift);
  `norm_T = norm_T_mul 1`; `exists_T_zpow_mul_ofInt`: from `exists_bound` take `k`, then
  `T^k * f` has bound `0`, i.e. `= ofInt x`, so `f = (T⁻¹)^k * ofInt x`; multiplicativity of a
  norm-1 unit `e`: `‖ex‖ ≤ ‖x‖` (`norm_mul_le`, `‖e‖ = 1`) and `‖x‖ = ‖e⁻¹(ex)‖ ≤ ‖e⁻¹‖‖ex‖ ≤ ‖ex‖`
  (`‖e⁻¹‖ ≤ 1` by `HaloInt.norm_le_one`); products: `‖abx‖ = ‖a‖‖bx‖ = ‖a‖‖b‖‖x‖`.
- **Mathlib lemmas needed**: `Units.ext`, `tsum_eq_single`, `norm_mul_le`, `zpow_neg`.
- **Sources**: [JN] Def 2.1.2 (`jn.txt` 483–490), p. 8 remark (493–494).
- **Generality**: `IsTate` instance global (no `p ≠ 2`).

### [CLEANUP-A] /cleanup on PhD/LWX/HaloTate.lean (3rd proof ticket + final)
- **Status**: done (finished 2026-09-05T15:40Z) | **Depends on**: A3 | **Type**: cleanup
- **Progress**:
  - 2026-09-05T15:40Z: DONE. Phase 0 baseline green; Phase 3: module docstring rewritten (no
    "SKELETON"), 2 dividers stripped, `=>`→`↦`; Phase 4: one `/cleanup` worker dispatched
    (`norm_mul_coeff_le`, 230k tokens) — the remaining ~60 declarations were audited and golfed
    inline by the main agent (budget decision for the 47-ticket marathon; same checklist:
    docstrings on public decls, none on private, line packing ≤ 100, `≤`/`<` orientation,
    STRUCTURE: `CommRing.mul_assoc` → `mul_assoc_aux`, `CompleteSpace` split into
    `lipschitzWith_coeff` + `exists_norm_le_zpow_of_cauchySeq`). Phase 5b renames (board-local
    `renames.jsonl`): `pR_pos → cast_p_pos`, `one_lt_pR → one_lt_cast_p`,
    `norm_mul₃_le → norm_mul₃_coeff_le`. Phase 6 gates: `lake build` full (3825 jobs) clean,
    runLinter: no findings in HaloTate.lean. Phase 6.5 `/simplify` (4 agents): applied —
    reuse `HaloInt.assocEquiv` (made public in HaloRing.lean), mathlib
    `isUltrametricDist_of_forall_norm_add_le_max_norm`, helpers `norm_mul_le_zpow` /
    `norm_single_le`, merged `NormedCommRing` instance, `coe_T` no longer `@[simp]`,
    `isMultiplicative_mul` moved to `TateFredholm.IsMultiplicative.mul` (Tate.lean; general).
    Skipped: generalising HaloRing's shift-0 lemmas to shifted bounds (HaloRing is a
    finished file), `Localization.Away` redesign (right altitude as is). Follow-up noted for
    F1: consider `coeff_T_zpow_mul` (ℤ-powers) since `TateRiesz.matrixCoeff_tateOp` uses
    `T ^ (a.2 - b.2 : ℤ)`. Result: 640 → 501 lines, sorry-free, std axioms.

## Tranche B — entire series (`PhD/TateFredholm/Entire.lean`)

### [B1] `IsEntire` API, subring, Leibniz rule
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/TateFredholm/Entire.lean | **Depends on**: none
  | **Parallel**: yes | **Type**: def + lemma
- **Progress**:
  - 2026-09-05T16:05Z: DONE. `hasseDeriv_mul` proved by *transfer from mathlib's
    `Polynomial.hasseDeriv_mul`* (new import `Mathlib.Algebra.Polynomial.HasseDeriv`): both sides'
    `coeff n` only see coefficients `≤ n + s`, so compare with `trunc (n + s + 1)`; `Finset.sum_congr`
    + `coeff_trunc` replace the truncated coefficients (no reindexing/Vandermonde needed). Closure lemmas
    are pointwise `isRestricted_*`; `IsEntire.hasseDeriv` via `PowerSeries.isRestricted_hasseDeriv`
    (un-privated in Riesz.lean, `omit [CompleteSpace R]`); added `isEntire_zero`. Section restructured:
    `[IsUltrametricDist R]` only from `IsEntire.mul` on, `[CompleteSpace R]` only for `evalT`.
    Build clean, axioms standard.
- **Statement**: `hasseDeriv_mul` (:42), `isEntire_iff` (:57), `IsEntire.tendsto_norm_coeff_mul_pow`
  (:63), `isEntire_C/one/X` (:67–74), `IsEntire.add/neg/sub/mul/pow/hasseDeriv` (:76–97),
  `Polynomial.isEntire_coe` (:99), `entireSubring.zero_mem'` (:110), `IsEntire.evalT_mul/add` (:119–127).
- **Proof sketch** (L-B1):
  1. `isEntire_iff`: `isRestricted_iff'` pointwise in `c`.  `tendsto_norm_coeff_mul_pow`: apply at
     `c = ‖a‖ + 1` and `tendsto_norm_coeff_mul_pow_of_isRestricted` (Riesz.lean:133).
  2. Closure lemmas: `isRestricted_C/one/X/…`, `isRestricted.add/neg/mul/pow` (Restricted/Basic:55–105)
     at each `c`.  `hasseDeriv`: un-private `PowerSeries.isRestricted_hasseDeriv` (Riesz.lean:237)
     or re-prove: `‖(n+k choose k) a_{n+k}‖c^n ≤ ‖a_{n+k}‖c^{n+k}·c^{−k}` (ultrametric: integer
     coefficients have norm `≤ 1`).
  3. `hasseDeriv_mul`: coefficientwise, `coeff n (hasseDeriv s (fg)) = (n+s choose s) ∑_{i+j=n+s} f_i g_j`
     and the RHS is `∑_{a+b=s} ∑_{i'+j'=n} (i'+a choose a)(j'+b choose b) f_{i'+a} g_{j'+b}`;
     reindex and use `Nat.add_choose_add`/Vandermonde `∑_{a+b=s} (i choose a)(j choose b) = (i+j choose s)`
     (`Nat.add_choose_eq`).  Mirror `Polynomial.hasseDeriv_mul` (mathlib HasseDeriv.lean:207).
  4. `evalT_mul/add`: `evalT_mul/add` with `tendsto_norm_coeff_mul_pow`.
- **Mathlib lemmas needed**: `PowerSeries.coeff_mul`, `Finset.sum_antidiagonal_eq_sum_range_succ`,
  `Nat.add_choose_eq`, `IsUltrametricDist.norm_natCast_le_one`.
- **Sources**: [Bel] Def II.1.16 (`bellaiche.txt` 2155–2158); [Buz07] p. 22 (`buzzard.txt` 786–800).
- **Generality**: `hasseDeriv_mul` over `CommSemiring`; the rest over ultrametric `NormedCommRing`.

### [B2] Euclidean division in `R{{T}}` ([Bel] Prop II.2.8)
- **Status**: done (finished 2026-09-05T16:40Z) | **File**: PhD/TateFredholm/Entire.lean | **Depends on**: B1 | **Parallel**: yes (with B3 after B1? no — B3 needs B2) | **Type**: lemma
- **Statement**: `IsEntire.exists_eq_mul_add` (:149), `eq_mul_add_q_unique` (:156), `eq_mul_add_r_unique` (:163).
- **Progress**:
  - 2026-09-05T16:40Z: DONE as sketched. Private helpers: `restrictedOf` (Riesz.lean's pattern),
    `distRadius B := 1 + ∑_{i ≤ deg} ‖bᵢ‖` with `one_le_distRadius`/`norm_coeff_le_distRadius`,
    `isMulDistinguished_of_monic` (Gauss norm `= c^s` at every `c ≥ distRadius B` via
    `Restricted.norm_le_iff` + `norm_coeff_mul_pow_le`), `exists_eq_mul_add_of_monic_of_le`
    (Weierstrass at radius `c`, unpacked by `congrArg Subtype.val`), `q_unique_of_monic_of_le`
    (`weierstrassDivision_q_unique_of_isMulDistinguished` with `Subtype.ext rfl`/`Subtype.ext h`),
    `exists_eq_mul_add_of_monic` (entire quotient by uniqueness at `max (distRadius B) c`),
    `monic_C_inv_mul`. Riesz.lean's `isRestricted_of_le` un-privated. Axioms standard.
- **Proof sketch** (L-B2):
  1. Reduce to monic: `B = u·B₀` (`u = leadingCoeff B`, `B₀ = C u⁻¹ * B` monic); divide by `B₀`,
     set `q = u⁻¹ q₀`.
  2. Choose `c ≥ max(1, max_i ‖(B₀).coeff i‖)`; then `‖toRestricted c B₀‖ = c^s` (Gauss norm attained
     at the top coefficient: `Polynomial.norm_toRestricted`, GaussNorm.lean:293) so
     `isMulDistinguished_toRestricted_of_monic` applies; `weierstrassDivision_exists_of_isMulDistinguished`
     on `⟨F, hF c hc⟩` gives `q_c ∈ Restricted R c`, `r`.
  3. Entireness of `q`: for `c' ≥ c` divide again; both are divisions at radius `c`
     (`isRestricted_of_le`), so `weierstrassDivision_q_unique_of_isMulDistinguished` gives `q_{c'} = q_c`,
     hence `q_c` is restricted at every `c' ≥ c`, hence at every radius.  (Pattern:
     `exists_factor_of_evterm_eq_zero`, Riesz.lean:439–447.)
  4. Uniqueness: pick a radius where `B₀` is distinguished and both quotients are restricted;
     `weierstrassDivision_q_unique/…_r_unique_of_isMulDistinguished`.
- **Mathlib lemmas needed**: `Polynomial.Monic`, `Polynomial.leadingCoeff_C_mul`, `Polynomial.degree_lt_iff_coeff_zero`.
- **Sources**: [Bel] Prop II.2.8 (`bellaiche.txt` 2380–2445).
- **Generality**: divisor with unit leading coefficient (source: "dominant term invertible").

### [B3] Relative primality and [Bel] Cor II.2.9
- **Status**: done (finished 2026-09-05T17:05Z) | **File**: PhD/TateFredholm/Entire.lean | **Depends on**: B2 | **Parallel**: no | **Type**: def + lemma
- **Statement**: `IsEntireCoprime.symm` (:174), `.mul_right` (:180),
  `isEntireCoprime_iff_isCoprime_of_eq_mul_add` (:187), `isCoprime_of_mul_add_eq_one` (:196).
- **Progress**:
  - 2026-09-05T17:05Z: DONE as sketched (`linear_combination` for every identity). Two statement
    adjustments: (i) `IsEntireCoprime.mul_right` needs `hF hG hG' : IsEntire _` (the witness
    `a a' F + a b' G' + b a' G` is entire only if the three series are — the skeleton lacked them,
    `IsEntireCoprime` itself does not force entireness); (ii) `isEntireCoprime_iff_isCoprime_of_eq_mul_add`
    does not need `r.degree < B.degree` — dropped (strictly more general). Degree-0 divisor case of
    `isCoprime_of_mul_add_eq_one` handled separately (`B = C u` is a unit polynomial). Axioms standard.
- **Proof sketch** (L-B3):
  1. `symm`: swap; `mul_right`: from `aF + bG = 1`, `a'F + b'G' = 1`: `(a + a'bG… )` — standard
     `IsCoprime.mul_right` computation: `1 = (aF + bG)(a'F + b'G') = F(…) + (bb')GG'`.
  2. `isCoprime_of_mul_add_eq_one`: divide `c` by `B` (B2): `c = Bc₁ + c₂`; divide `c₂B + ar`…
     precisely: from `cB + ar = 1` write `ar = B·d + e` (polynomial division, `e` of degree `< deg B`)
     then `(c + d)B + e = 1`; uniqueness of the division of `1` by `B` (`1 = B·0 + 1`) forces `e = 1`
     and `c + d = 0`, so `(−d)B + ar = 1` with polynomial coefficients.
  3. `iff`: `(⇐)` `aB + br = 1 ⇒ aB + b(F − Bq) = (a − bq)B + bF = 1`; `(⇒)` `aB + bF = 1 ⇒
     (a + bq)B + b r = 1`, then step 2 with `c = a + bq`.
- **Mathlib lemmas needed**: `IsCoprime`, `Polynomial.modByMonic/divByMonic` (after unit
  rescaling) or `Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff` (MulWeierstrassDivision.lean:123).
- **Sources**: [JN] Def 2.2.1 (`jn.txt` 660–666); [Bel] Cor II.2.9 (`bellaiche.txt` 2446–2448).
- **Generality**: as stated.

### [CLEANUP-B1] /cleanup on PhD/TateFredholm/Entire.lean (after 3rd proof ticket)
- **Status**: done (finished 2026-09-05T17:20Z) | **Depends on**: B3 | **Type**: cleanup
- **Progress**:
  - 2026-09-05T17:20Z: DONE (inline audit by the main agent, same economy as CLEANUP-A; the
    `/simplify` agent pass is deferred to CLEANUP-B2 since B4 still edits this file). Module
    docstring rewritten (no "SKELETON"; Main definitions/results/references), 6 private docstrings
    stripped, 2 long lines wrapped, every unused section variable `omit`ted, new import
    `Mathlib.Algebra.Polynomial.HasseDeriv`. Gates: module build clean, runLinter no findings in
    Entire.lean, full `lake build` (3825 jobs) clean.

### [B4] Good zeros, factorisation, identity theorem
- **Status**: done (finished 2026-09-05T18:10Z) | **File**: PhD/TateFredholm/Entire.lean | **Depends on**: CLEANUP-B1 | **Parallel**: yes (with C4) | **Type**: lemma
- **Statement**: `IsEntire.eq_zero_of_forall_evalT_pow_eq_zero` (:133), `IsGoodZero.isUnit` (:214),
  `.mul` (:220), `.of_mul` (:226), `.exists_factor` (:232).
- **Progress**:
  - 2026-09-05T18:10Z: DONE, Entire.lean sorry-free (axioms standard). New public API: `IsEntire.sum`,
    `IsEntire.shift` (coefficient shift `mk fun n ↦ coeff (n + m) f` stays entire), `IsEntire.evalT_sub`,
    `evalT_zero`, `evalT_X_pow`, `IsEntire.evalT_sum`, `IsEntire.evalT_hasseDeriv_mul` (Leibniz at a
    point). Identity theorem: factor `f = X^n₀ g` with `n₀ = Nat.find`, cancel the unit `(ϖ^k)^n₀`,
    then `‖g₀‖ ≤ M ‖ϖ‖^k` via `Summable.tsum_eq_zero_add` + `TateFredholm.norm_tsum_le_iSup`
    (only `‖ϖ‖ < 1` and unit-ness of `ϖ` are used, not multiplicativity). Good zeros: private
    `evalT_hasseDeriv_mul_eq_of_forall_lt` (`Δⁱ(FG)(a) = ΔⁱF(a)G(a)` once lower derivatives vanish)
    drives `.mul`/`.of_mul` (strong induction); `exists_factor` by induction on `s` with B2's division
    by the *polynomial* `C (-u⁻¹) X + C 1` (leading coefficient via `leadingCoeff_linear`), remainder
    forced to `0` by evaluation, and the private peeling lemma `isGoodZero_of_one_sub_C_mul_X_mul`
    (uses `hasseDeriv j (1 - C b X) = [1 - C b X, C (-b), 0, …]`). Riesz.lean: `evalT_X` and
    `evalT_sub'`→`evalT_sub` made public.
- **Proof sketch** (L-B4):
  1. Identity theorem: suppose `f ≠ 0`, `n₀` minimal with `d := coeff n₀ f ≠ 0`.  From
     `evalT (ϖ^k) f = 0`: `d·ϖ^{kn₀} = −∑_{n>n₀} d_n ϖ^{kn}`; multiply by `ϖ^{−kn₀}` (unit,
     multiplicative): `‖d‖ ≤ sup_{n>n₀} ‖d_n‖‖ϖ‖^{k(n−n₀)} ≤ (sup_n ‖d_n‖)·‖ϖ‖^k → 0`
     (`norm_tsum_le_iSup`, entire ⇒ bounded coefficients, `‖ϖ‖ < 1`), so `d = 0`.
  2. `isUnit`: `F(a) = 0`, `F(0) = 1` ⇒ `1 = −a·(a_1 + a_2a + ⋯)` (`evalT` of `F − 1 = X·G`) — the
     cofactor is `evalT a` of the entire `mk (fun n ↦ a_{n+1})`.
  3. `mul`/`of_mul`: Leibniz `hasseDeriv_mul` + `evalT_add/mul` (entire factors): for `i < s`
     all terms `Δ^jF(a)Δ^{i−j}G(a)` vanish; at `i = s` only `Δ^sF(a)·G(a)` survives, a unit iff
     `Δ^sF(a)` is (given `G(a)` unit).  `of_mul` by induction on `i`.
  4. `exists_factor`: induction on `s` via B2 division by `1 − u⁻¹X` (leading coefficient
     `−u⁻¹`, a unit): `F = (1 − u⁻¹X)G₁ + r`, `r` constant `= F(u) = 0`; `u` is a good zero of
     `G₁` of order `s − 1` by `of_mul`-type transfer (`Δ^i((1−u⁻¹X)G₁)(u)` expands, using
     `evalT_hasseDeriv_pow_mul_of_lt` (Riesz.lean:330) pattern); at `s = 0` take `G = F`.
- **Mathlib lemmas needed**: `PowerSeries.coeff_mul_X`, `Finset.sum_antidiagonal_succ`, `IsUnit.mul_iff`.
- **Sources**: [Bel] Def II.2.11, Ex II.2.12, §II.2.3 (`bellaiche.txt` 2470–2480); [Buz07] p. 20.
- **Generality**: identity theorem needs `[Nontrivial R]` and a pseudo-uniformizer only.

### [CLEANUP-B2] /cleanup on PhD/TateFredholm/Entire.lean (final)
- **Status**: done (finished 2026-09-05T19:05Z) | **Depends on**: B4 | **Type**: cleanup
- **Progress**:
  - 2026-09-05T19:05Z: DONE (inline audit + `/simplify` 4-agent pass, ≈760k tokens). STRUCTURE:
    identity theorem split into `norm_coeff_zero_le_of_evalT_eq_zero` (+ mathlib's
    `divXPowOrder`/`X_pow_order_mul_divXPowOrder` replacing a hand-rolled `Nat.find` factoring);
    `[Nontrivial R]` dropped from it (unused). Simplify applied: reuse Riesz.lean's `restrictedOf`
    and `hasseDeriv_one_sub_C_mul_X_mul` (both made public), shared `isEntire_one_sub_C_mul_X` /
    public `evalT_one_sub_C_mul_X`, `Finset.cons_induction` (no `classical`), `htrunc` hoist, `rwa`,
    `omit`s on defs, hoisted repeated terms; NEW public converse `IsGoodZero.of_factor`
    (needed by C-tickets' `isGoodZero_dSeries_bQ`). Deferred (recorded, not done): promoting
    `distRadius`/`isMulDistinguished_of_monic` into MulDistinguished.lean (E1 may want it — do it
    then), `IsGoodZero` as a structure, moving `hasseDeriv_mul` to a ForMathlib HasseDeriv file,
    restating the identity theorem for any unit of norm `< 1`. Gates: module build clean,
    runLinter clean for Entire.lean, full `lake build` (3825 jobs) clean. 647 → 627 lines.

## Tranche R — `Res(charpoly A, g) = det g(A)` (`PhD/TateFredholm/Resultant.lean`)

### [R1] The resultant of the characteristic polynomial
- **Status**: done (finished 2026-09-05T19:50Z) | **File**: PhD/TateFredholm/Resultant.lean | **Depends on**: none | **Parallel**: yes | **Type**: lemma (mathlib PR candidate)
- **Statement**: `Matrix.det_aeval_eq_prod_roots` (:36), `Matrix.resultant_charpoly` (:43).
- **Progress**:
  - 2026-09-05T19:50Z: DONE, Resultant.lean sorry-free, axioms standard. `det_aeval_eq_prod_roots`:
    both sides are monoid homs in `g` (`detMonoidHom ∘ aeval A` vs `g ↦ ∏_λ g(λ)`), so it reduces to
    `g = C c` (`det (c • 1) = c^n`) and `g = X - C μ` (`det (A - μ) = (-1)^n charpoly A (μ)` via
    `eval_charpoly`, `det_neg`, `Multiset.prod_map_neg`). New intermediate
    `resultant_charpoly_of_splits` = mathlib's `resultant_eq_prod_eval` (needs only `charpoly` to split)
    + the det lemma. General case: universal ring `MvPolynomial (n × n ⊕ ℕ) ℤ` (no `let` for the ring —
    `simp` cannot see through a `let`-bound type when rewriting `eval₂Hom`), `G = ∑_{k ≤ m} C (X (inr k)) X^k`,
    identity checked in `AlgebraicClosure (FractionRing _)` (injective via `IsScalarTower.algebraMap_eq`),
    transported by `resultant_map_map`, `charpoly_map`, `RingHom.map_det`, `map_aeval_eq_aeval_map`
    (with the private `algebraMap_comp_eq_mapMatrix_comp`), then specialised by `eval₂Hom` (`as_sum_range'`).
- **Proof sketch** (L-R1, L-R2):
  1. Domain case: `g = C c * ∏_{μ ∈ g.roots} (X − C μ)` (`Splits.eq_prod_roots`); `aeval A` is a
     ring hom so `aeval A g = c • ∏ (A − scalar μ)`; `det` multiplicative;
     `det (A − scalar μ) = (−1)^n det (scalar μ − A) = (−1)^n eval μ (charpoly A)` (`eval_charpoly`,
     `det_neg`); `eval μ (charpoly A) = ∏_{λ ∈ roots} (μ − λ)` (charpoly monic, splits); regroup the
     double product to `∏_λ (c ∏_μ (λ − μ)) = ∏_λ g(λ)`.
  2. Universal case: `S := MvPolynomial (n × n ⊕ Fin (m+1)) ℤ`, `U := Matrix.of (X ∘ inl)`,
     `G := ∑ k, C (X (inr k)) * X^k`; `K := AlgebraicClosure (FractionRing S)`; over `K` both
     `charpoly (U.map _)` and `G.map _` split (`IsAlgClosed.splits`), so `resultant_eq_prod_eval`
     (Resultant/Basic:479, leading coefficient `1`, `hg`) + step 1 give the identity in `K`;
     `resultant_map_map`, `RingHom.map_det`, `Polynomial.aeval_map_algebraMap`/`charpoly_map`
     pull it back to `S` (injective `S → K`), then push to `R` along `eval₂Hom` with `A` and `g`'s
     coefficients (`univ_map_eval₂Hom`-style or directly `charpoly_map`).
- **Mathlib lemmas needed**: `Polynomial.Splits.eq_prod_roots`, `Matrix.eval_charpoly`,
  `Matrix.det_neg`, `Matrix.det_mul`, `Finset.prod_comm`, `Multiset.prod_map_mul`,
  `Polynomial.resultant_eq_prod_eval`, `Polynomial.resultant_map_map`, `Matrix.charpoly_map`,
  `IsAlgClosed.splits`, `MvPolynomial` domain instance, `IsFractionRing.injective`.
- **Sources**: [Bel] Prop II.2.16 proof, Lemma II.2.13 proof (`bellaiche.txt` 2508–2513, 2543–2554).
- **Generality**: any `CommRing`; degree parameter `Fintype.card n`.

### [CLEANUP-R] /cleanup on PhD/TateFredholm/Resultant.lean (final)
- **Status**: done (finished 2026-09-05T20:20Z) | **Depends on**: R1 | **Type**: cleanup
- **Progress**:
  - 2026-09-05T20:20Z: DONE (inline audit + one combined simplify reviewer). Restructured for the
    mathlib PR: the MonoidHom argument is now the private bootstrap `det_aeval_eq_prod_roots_of_splits`,
    `resultant_charpoly_of_splits` is private, and the public `det_aeval_eq_prod_roots` no longer
    needs `g.Splits` (it is a corollary of `resultant_charpoly` + `resultant_eq_prod_eval`).
    Imports trimmed to `Charpoly.Coeff` + `Resultant.Basic` + `AlgebraicClosure`; private helper
    golfed via `Matrix.diagonal_map`; module docstring finalised. Reviewer confirmed: no mathlib
    counterpart exists; `Fintype.card n` (not `natDegree`, which needs `Nontrivial`) and `IsDomain`
    (not `Field`) are the right shapes. PR note: `det_aeval_eq_prod_roots` belongs in
    `Charpoly/Eigs.lean`, `resultant_charpoly` in a new `Resultant/Charpoly.lean`. Gates clean.

## Tranche C — Coleman's `D` (`PhD/TateFredholm/Coleman.lean`)

### [C1] `dPoly`: basic identities and multiplicativity
- **Status**: done (finished 2026-09-05T20:50Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: none | **Parallel**: yes | **Type**: def + lemma
- **Statement**: `bQ_coeff_zero` (:60), `natDegree_bQ` (:64), `dPoly_coeff_zero` (:69), `dPoly_succ`
  (:75), `dPoly_mul` (:81).
- **Progress**:
  - 2026-09-05T20:50Z: DONE as sketched (axioms standard). Private helpers `natDegree_gPoly_le`,
    `gPoly_coeff_zero`, `natDegree_reflect_eq`, `reflect_succ_of_natDegree_le`, `natDegree_map_C_reflect`;
    `dPoly_coeff_zero` via `resultant_map_map (evalRingHom 0)` + `resultant_one_right`; `dPoly_succ`/`dPoly_mul`
    via `resultant_mul_left` after `nontriviality R` (degree parameters must be exact natDegrees).
- **Proof sketch** (L-C1):
  1. `bQ_coeff_zero`: `coeff 0 (Q.reverse) = leadingCoeff Q = u` (`coeff_zero_reverse`), so
     `1 − u⁻¹·u = 0`.  `natDegree_bQ`: `natDegree Q.reverse = natDegree Q` when `Q.coeff 0 ≠ 0`
     (`reverse_natDegree`, `natTrailingDegree_eq_zero`).
  2. `dPoly_coeff_zero`: apply `resultant_map_map` along `eval 0 : R[T] → R`: `gPoly B ↦ 1`, then
     `resultant_add_right_deg` reduces the degree parameter of the constant `1` from `deg B` to `0`
     picking up `(coeff N (reflect N P))^{deg B} = (P.coeff 0)^{deg B} = 1`, and `resultant_C_zero_right`.
  3. `dPoly_succ`: `reflect (N+1) P = X * reflect N P` (`coeff_reflect`/`revAt` or
     `reflect_C_mul_X_pow` termwise); `natDegree (X * reflect N P) = 1 + N` (unit constant
     coefficient, nontrivial ring; trivial ring separately); `resultant_mul_left X (reflect N P) g`
     and `resultant_X_pow_left g 1 _ : Res(X, g) = g.coeff 0 = 1` (`gPoly` has constant coefficient `1`
     iff `B.coeff 0 = 0`).
  4. `dPoly_mul`: `reflect (N+M) (PQ) = reflect N P * reflect M Q` (`reflect_mul`), natDegrees add
     (unit constant coefficients), `resultant_mul_left`.
- **Mathlib lemmas needed**: `Polynomial.coeff_zero_reverse`, `reverse_natDegree`, `reflect_mul`,
  `reflect_C_mul_X_pow`, `resultant_mul_left`, `resultant_X_pow_left`, `resultant_add_right_deg`,
  `resultant_C_zero_right`, `resultant_map_map`, `Polynomial.natDegree_mul'`.
- **Sources**: [Buz07] p. 21 (`buzzard.txt` 738–748); [Bel] Lemma II.2.13 (i) (`bellaiche.txt` 2500–2515).
- **Generality**: `CommRing`; hypotheses `IsUnit (P.coeff 0)`, `B.coeff 0 = 0` as the source's
  `P(0) = 1`, `Q(0) = 0`.

### [C2] `(ii)`, `(iii)`, the unit criterion, finite spectral mapping
- **Status**: done (finished 2026-09-05T21:45Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: C1, R1 | **Parallel**: yes (with C3) | **Type**: lemma
- **Statement**: `dPoly_bQ_self` (:88), `eval_one_dPoly_bQ` (:94), `eval_one_dPoly_bQ_add_mul` (:102),
  `isCoprime_reflect_reverse_iff` (:110), `isUnit_eval_one_dPoly_bQ_iff` (:118), `Matrix.charpolyRev_aeval` (:126).
- **Progress**:
  - 2026-09-05T21:45Z: DONE (axioms standard). Statement adjustments: `eval_one_dPoly_bQ` needs
    `hQ0`, `hu` (its degree parameter is `Q.natDegree = (bQ Q u).natDegree`); `eval_one_dPoly_bQ_add_mul`
    does not need `hP`; `Matrix.charpolyRev_aeval` does not need `B.coeff 0 = 0` (R1 gives it for every
    `B`). Private helpers: `natDegree_reflect_le_of_le`, `reflect_reflect` (reflect is an involution
    unconditionally, `revAt_invol`), `natDegree_reverse_eq`, `gPoly_bQ`, `isCoprime_X_of_isUnit_coeff_zero`
    (via `divX`), `isCoprime_of_X_pow_eq_add`, `X_pow_eq_reflect_add_reflect` (reflect a Bézout identity).
    Unit criterion via `resultant_C_mul_right`, `resultant_comm`, `resultant_add_right_deg` (padding), mathlib's
    `isUnit_resultant_iff_isCoprime` for the monic `Q.reverse`. **Elaboration trap (recorded for C3–C6):**
    any `rw` whose pattern head is `Polynomial.map`/`HMul` in a goal containing both `gPoly (bQ Q u)`
    and `(reflect N P).map C` (or `C u⁻¹ * Q.reverse`) makes `kabstract`'s `isDefEq` unfold
    `reflect`/`reverse` into `Finsupp` and hit the heartbeat limit — use explicit `congrArg (fun x ↦ …) h`
    steps instead (see `eval_one_dPoly_bQ`, `eval_one_dPoly_bQ_add_mul`). Also: an error reported at
    column 0 of a docstring line belongs to the declaration *below* it.
- **Proof sketch** (L-C2):
  1. `(ii)`: `gPoly (bQ Q u) = (1 − T) + T·u⁻¹·Q.reverse(X)` in `(R[T])[X]`; `resultant_add_mul_right`
     with `f = Q.reverse` (map `C`), `p = C(T u⁻¹)` (X-degree `0 ≤ … `), parameters `(n, n)`:
     `= Res(Q.reverse, C(1 − T))(n, n)`; `resultant_add_right_deg` from `(n, 0)`:
     `(coeff n Q.reverse)^n·Res(Q.reverse, C(1−T))(n,0) = 1·(1 − T)^n` (`resultant_C_zero_right`).
  2. `eval_one_dPoly_bQ`: `resultant_map_map` along `Polynomial.evalRingHom 1` (`gPoly ↦ 1 − 1·bQ = u⁻¹Q.reverse`).
  3. `(iii)`: after step 2 both sides are resultants against `u⁻¹Q.reverse`; `reflect N (P + C'Q) =
     reflect N P + reflect (N−n) C' * reflect n Q` (`reflect_add`, `reflect_mul`) and
     `reflect n Q = Q.reverse = u·(u⁻¹Q.reverse)`; `resultant_add_mul_left` with `p = u·reflect (N−n) C'`
     (`natDegree ≤ N − n`, so `natDegree p + n ≤ N`).
  4. `isCoprime_reflect_reverse_iff`: `(⇐)`: reflect a Bézout identity `aP + bQ = 1` at degree
     `M ≥ deg a + N, deg b + n`: `X^M = reflect a·reflect_N P + reflect b·Q.reverse`; `(X, Q.reverse)`
     coprime (`Q.reverse.coeff 0 = u` unit) hence `(X^M, Q.reverse)` coprime; combine.  `(⇒)`:
     symmetric using `reflect N (reflect N P) = P` (`natDegree P ≤ N`; prove via `coeff_reflect`,
     `revAt_invol`) and `(X, Q)` coprime (`Q.coeff 0 = 1`).
  5. Unit criterion: step 2, `resultant_C_mul_right` (factor `(u⁻¹)^N`), `resultant_comm` (sign),
     `isUnit_resultant_iff_isCoprime (hf : Q.reverse.Monic)` (`Monic` from `reverse_leadingCoeff` =
     `trailingCoeff Q = Q.coeff 0 = 1`), step 4.
  6. `charpolyRev_aeval` (do not route through `reverse (charpoly (aeval A B))`; go the
     other way): `dPoly B A.charpolyRev (card n) = Res(reflect (card n) (charpolyRev A), gPoly B)` and
     `reflect (card n) (charpolyRev A) = charpoly A` (`reverse_charpoly` + reflect of reverse at the
     natDegree = `card n`); then `Matrix.resultant_charpoly A (gPoly B)` over `R[T]` (apply R1 to
     `A.map C` over `R[T]`, `charpoly_map`) gives `det (aeval (A.map C) (gPoly B)) = det (1 − T·(aeval A B).map C)
     = charpolyRev (aeval A B)` (`aeval` of `1 − C T * B.map C` at `A.map C` is `1 − T • (aeval A B).map C`).
- **Mathlib lemmas needed**: as listed in decomposition L-C2 plus `Polynomial.revAt_invol`,
  `Polynomial.Monic.def`, `Matrix.charpoly_map`, `Matrix.charpolyRev`, `Polynomial.aeval_algebraMap_apply`.
- **Sources**: [Bel] Lemma II.2.13 (ii)–(iii) (`bellaiche.txt` 2500–2520); [JN] Lemma 2.2.7 proof
  citing [Col97, Lemma A3.7] (`jn.txt` 730–732); [Bel] Prop II.2.16 (2543–2554).
- **Generality**: `CommRing`.

### [C3] Estimates: crude bound, multilinearity, scaling, entireness bound
- **Status**: done (finished 2026-09-05T23:40Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: C1 | **Parallel**: yes (with C2) | **Type**: lemma
- **Statement**: `norm_coeff_dPoly_le` (:141), `norm_coeff_dPoly_sub_le` (:150), `dPoly_comp_C_mul_X`
  (:158), `dPoly_C_mul` (:166), `norm_coeff_dPoly_le_pow` (:172).
- **Progress**:
  - 2026-09-05T23:40Z: DONE (axioms standard). Route differs from the sketch in two places.
    (i) Crude bound: general private `gaussNorm_det_le` (Gauss norm of a determinant ≤ product of
    per-column bounds; `det_apply'`, ultrametric sum ≤ max, `gaussNorm_prod_le`, sign of norm 1),
    applied to the Sylvester matrix at radius `Cb⁻¹`; hypotheses weakened to `0 ≤ C`, `0 < Cb`.
    (ii) Multilinearity: `MultilinearMap.map_add_univ` on `detRowAlternating` of the transposed
    Sylvester matrix (`S' = S + D`, `D = sylvester (F' − F) 0`), each non-`univ` subset term bounded by
    `δ C^{d−1}` by `gaussNorm_det_le` (a missing `gPoly` column ⇒ zero column ⇒ `det = 0`).
    (iii) Scaling: instead of `scaleRoots`, the **diagonal conjugation** identity
    `dPoly_eq_dPoly_comp : dPoly B P N = dPoly (B.comp (C λ X)) (P.comp (C λ⁻¹ X)) N` (`diag(λⁱ) S diag(λ⁻ʲ)`
    is the Sylvester matrix of the scaled polynomials; `det_diagonal`); `dPoly_comp_C_mul_X` follows
    without its `hP`/`hP0` hypotheses (dropped), `dPoly_C_mul` needs `lam : Rˣ` (the `lam : R` statement
    is false at `lam = 0`; fixed) and is proved with `compRingHom` + `resultant_map_map`. (iv) Entireness
    bound: conjugation + crude bound at radius `(‖ϖ‖^m Cb)⁻¹` — `dPoly_C_mul` is not needed; the
    hypotheses `hP`, `hP0` were unused and dropped. New general `TateFredholm.IsMultiplicative.norm_pow_mul`
    in Tate.lean. Traps recorded: `Finset.piecewise` on `Matrix`-typed rows does not type-check for
    `rw` (use function-typed rows + `Matrix.of`); `ᵀ` notation is scoped to `Matrix`; `rw [← resultant_map_map]`
    in a goal containing `C lam` makes the unifier unfold the resultant (use `Eq.trans ?_ (resultant_map_map …)`);
    `hF`/`hG` closed by `rw`, not `simp only` (simp made no progress, cause unknown).
- **Proof sketch** (L-C3):
  1. Crude bound: `Polynomial.resultant = det (sylvester …)`; `Matrix.det_apply`; work with the
     Gauss norm `‖·‖_ρ` on `R[T]` at `ρ = Cb⁻¹` (ForMathlib `Polynomial.gaussNorm`, ultrametric,
     `gaussNorm_mul_le`): every Sylvester entry has `‖·‖_ρ ≤ max 1 C` (f-rows: coefficients of
     `reflect N P`; g-rows: `1`, `−T b_k` with `‖T b_k‖_ρ = ‖b_k‖ρ ≤ 1`, or `0`); a permutation term
     is a product of `N + deg B` entries of which exactly `deg B` come from f-rows ⇒
     `‖term‖_ρ ≤ C^{deg B}`; ultrametric sum ⇒ `‖det‖_ρ ≤ C^{deg B}`; read off `‖coeff j‖ρ^j ≤ ‖det‖_ρ`.
     (Set up a lemma "product of polynomials with `‖·‖_ρ`-bounds" once.)
  2. Multilinearity: the Sylvester matrix of `reflect N P` vs `reflect N P'` differ only in the
     `deg B` f-rows; telescope `det M' − det M = ∑_r det (rows < r from M', row r from M' − M, rows > r from M)`
     (`Matrix.det_updateRow_add` / `det_updateRow_sub`); each mixed determinant has one row with
     entries `p'_k − p_k` (`‖·‖ ≤ δ`) and `deg B − 1` f-rows bounded by `C`; step 1's bound gives
     `δ C^{deg B − 1} Cb^j`.
  3. `dPoly_comp_C_mul_X`: `reflect N (P.comp (C λ * X)) = (reflect N P).scaleRoots λ` (`coeff_scaleRoots`
     + `coeff_reflect`, `natDegree (reflect N P) = N`); `gPoly B = (g').scaleRoots λ` for
     `g' = C(λ^{−deg B}) * gPoly (B.comp (C λ * X))` (`coeff_scaleRoots`: `g'_i λ^{deg B − i}`);
     `resultant_scaleRoots` and `resultant_C_mul_right` cancel the `λ` powers.
  4. `dPoly_C_mul`: `resultant_map_map` along `T ↦ λT` (`Polynomial.compRingHom`/`eval₂RingHom`).
  5. Entireness bound: `y_k := p_k ϖ^{−mk}` (`‖y_k‖ ≤ C`); `P = P_y.comp (C ϖ^m * X)`; step 3 gives
     `dPoly B P N = dPoly (B.comp (C ϖ^m X)) P_y N`; `B.comp (C ϖ^m X) = C ϖ^m * B'` with
     `B' = ∑ b_i ϖ^{m(i−1)} X^i` (`B(0) = 0`), `‖B'.coeff i‖ ≤ Cb`; step 4:
     `coeff j = ϖ^{mj}·coeff j (dPoly B' P_y N)`; step 1 bound and `‖ϖ^{mj}·x‖ = ‖ϖ‖^{mj}‖x‖`
     (multiplicativity).
- **Mathlib lemmas needed**: `Polynomial.resultant` unfolding to `sylvester`, `Matrix.det_apply`,
  `Matrix.det_updateRow_add`, `Finset.prod` bounds, `Polynomial.coeff_scaleRoots`, `natDegree_scaleRoots`,
  `resultant_scaleRoots`, `resultant_C_mul_right`, `resultant_map_map`, `Polynomial.comp`, `coeff_comp_C_mul_X`-type
  lemmas (`Polynomial.coeff_comp_degree_mul_degree`? use `Polynomial.comp_C_mul_X_coeff`),
  `PseudoUniformizer.isMultiplicative`, `TateFredholm.PseudoUniformizer.norm_zpow`.
- **Sources**: [Bel] p. 68 (`bellaiche.txt` 2521–2527); [Buz07] p. 21 (`buzzard.txt` 748–760).
- **Generality**: `1 ≤ C, Cb` normalisations as the source's unit-ball renormalisation.

### [CLEANUP-C1] /cleanup on PhD/TateFredholm/Coleman.lean (after 3rd proof ticket)
- **Status**: done (finished 2026-09-06T00:20Z) | **Depends on**: C3 | **Type**: cleanup
- **Progress**:
  - 2026-09-06T00:20Z: DONE (inline, no subagents per user instruction). Two docstrings that had
    drifted onto private helpers (`dPoly_bQ_self`, `isCoprime_reflect_reverse_iff`) moved back;
    private docstrings → `--` comments; 3 long lines wrapped; STRUCTURE: `gaussNorm_dPoly_sub_le`
    (99 lines) split into `gaussNorm_det_piecewise_le` (per-subset column bound) + the expansion;
    `norm_coeff_dPoly_le_pow` lost an unused `[IsTate R]` (linter). Module docstring marker
    removed (final pass at CLEANUP-C2). Gates: module build clean, runLinter clean for Coleman.lean,
    full `lake build` clean.

### [C4] `dSeries`: convergence, Lipschitz, entireness, multiplicativity
- **Status**: done (finished 2026-09-06T02:10Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: CLEANUP-C1, B1 | **Parallel**: yes (with B4) | **Type**: def + lemma
- **Statement**: `tendsto_coeff_dPoly_trunc` (:188), `dSeries_coe` (:197), `norm_coeff_dSeries_sub_le`
  (:203), `IsEntire.dSeries` (:216), `dSeries_mul` (:223).
- **Progress**:
  - 2026-09-06T02:10Z: DONE (axioms standard). Private helpers: `exists_coeff_bound` (polynomial
    coefficients bounded by `1 + ∑‖bₖ‖`), `norm_sum_le_of_forall_le` (ultrametric finite sums),
    `cauchySeq_of_norm_sub_succ_le` (ultrametric Cauchy criterion: successive differences → 0,
    via `Finset.sum_range_sub` telescoping), `exists_norm_coeff_mul_pow_le` (entire ⇒ `‖aₖ‖cᵏ ≤ C`),
    `norm_coeff_trunc_le`, `isUnit_coeff_zero_trunc`, `dPoly_eq_of_le` (iterated `dPoly_succ`).
    `dSeries_mul` uses explicit geometric tails: entire series satisfy `‖aₖ‖ ≤ C (1/2)ᵏ`, so
    `‖coeff k (FG − P_N Q_N)‖ ≤ C_F C_G (1/2)^N` uniformly (`coeff_mul_eq_coeff_trunc_mul_trunc₂` for
    `k ≤ N`), then the Lipschitz bound and `dSeries_coe` + `dPoly_mul` on the truncations; limits
    identified by `tendsto_nhds_unique`. Trap: inside `theorem IsEntire.dSeries`, bare `dSeries`
    resolves to the theorem itself — write `Coleman.dSeries`.
- **Proof sketch** (L-C4):
  1. Cauchy: `trunc (N+2) F = trunc (N+1) F + C a_{N+1} X^{N+1}`; `dPoly B (trunc (N+2) F) (N+1)` vs
     `dPoly B (trunc (N+1) F) (N+1)` (the latter `= dPoly B (trunc (N+1) F) N` by `dPoly_succ`):
     `norm_coeff_dPoly_sub_le` with `δ = ‖a_{N+1}‖ → 0`; complete ⇒ convergent;
     `Filter.Tendsto.limUnder_eq`.
  2. `dSeries_coe`: eventually constant sequence (`dPoly_succ`).
  3. Lipschitz: for each `N`, `norm_coeff_dPoly_sub_le` on the truncations (same `δ`), pass to
     the limit (`le_of_tendsto`).
  4. Entireness: for `σ > 0` pick `m` with `‖ϖ‖^m Cb < σ⁻¹`; `C_m := max 1 (sup_k ‖a_k‖‖ϖ‖^{−mk})`
     finite (entire); `norm_coeff_dPoly_le_pow` on every truncation (same `C_m`); limit ⇒
     `‖coeff j (dSeries)‖ ≤ C_m^{deg B}(‖ϖ‖^m Cb)^j`, so `‖coeff j‖σ^j → 0` (`isEntire_iff`).
  5. `dSeries_mul`: `trunc K F * trunc K G → FG` in coefficient sup-norm (tails: `sup_{k>K}` bounds)
     — but `dPoly_mul` needs polynomials: use `dPoly B (trunc F · trunc G) (2K) = dPoly B (trunc F) K · dPoly B (trunc G) K`
     and `dSeries B (trunc F·trunc G) = dPoly … (2K)` (`dSeries_coe`); Lipschitz (step 3) with
     `F' := trunc F · trunc G` and `δ_K → 0` ⇒ `dSeries B (FG) = lim dSeries B (trunc F·trunc G)
     = lim dPoly(trunc F)·dPoly(trunc G) = dSeries B F · dSeries B G` coefficientwise.
- **Mathlib lemmas needed**: `PowerSeries.trunc`, `coeff_trunc`, `trunc_succ`, `cauchySeq_of_le_geometric`-type
  or direct `Metric.cauchySeq_iff`, `cauchySeq_tendsto_of_complete`, `Filter.Tendsto.limUnder_eq`,
  `le_of_tendsto_of_tendsto`, `PowerSeries.coeff_mul`.
- **Sources**: [Bel] p. 68 + Ex II.2.2 (`bellaiche.txt` 2521–2530, 2364–2368); Lemma II.2.14 (i).
- **Generality**: entire inputs with constant term `1`.

### [C5] The unit criterion for entire series and [Bel] Prop II.2.15
- **Status**: done (finished 2026-09-06T03:05Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: C4, C2, B2, B3 | **Parallel**: no | **Type**: lemma
- **Statement**: `evalT_one_dSeries_bQ_eq_of_eq_mul_add` (:233), `isUnit_evalT_one_dSeries_bQ_iff` (:243),
  `isGoodZero_dSeries_bQ` (:252).
- **Proof sketch** (L-C5):
  1. Evaluation lemma: `S_N := trunc (N+1) S`; polynomial division `S_N = Q q_N + r_N` (Euclidean,
     unit leading coefficient); `(iii)` (C2) ⇒ `(dPoly (bQ) S_N N).eval 1 = (dPoly (bQ) r_N n).eval 1`.
     Continuity: `evalT 1 (dSeries (bQ) S) = lim_N (dPoly (bQ) S_N N).eval 1` by
     `tendsto_tsum_of_dominated_convergence` (Tannery.lean:40) with the uniform bound of C3/C4
     (entireness bound at `m` with `‖ϖ‖^m Cb < 1`, uniform in `N`) and coefficientwise convergence
     (`tendsto_coeff_dPoly_trunc`); `r_N → r`: `S − S_N = Q(q − q_N) + (r − r_N)` is a division of
     `S − S_N` (entire, `→ 0` in every Gauss norm) at a radius `c` where `Q` is distinguished, so
     `‖r − r_N‖_c ≤ ‖S − S_N‖_c → 0` (`norm_eq_max_of_eq_mul_add_of_isMulDistinguished`, MulWeierstrassDivision:71);
     `r ↦ (dPoly (bQ) r n).eval 1` is a polynomial in finitely many coefficients ⇒ continuous.
  2. Unit criterion: step 1 + `isUnit_eval_one_dPoly_bQ_iff` (C2) `⟺ IsCoprime r Q`
     `⟺ IsEntireCoprime Q S` (B3 `isEntireCoprime_iff_isCoprime_of_eq_mul_add`).
  3. II.2.15: `dSeries (bQ) (Q·S) = dSeries (bQ) Q · dSeries (bQ) S` (C4), `dSeries (bQ) Q = (1 − X)^n`
     (`dSeries_coe` + `dPoly_bQ_self`); `(1 − X)^n` has a good zero of order `n` at `1` (Hasse
     derivatives of `(1−X)^n`: `Δ^i (1−X)^n = (n choose i)(−1)^i (1−X)^{n−i}`, `evalT 1` = `0` for
     `i < n`, `(−1)^n` for `i = n`); `IsGoodZero.mul` (B4) with `G(1) = dSeries (bQ) S (1)` a unit
     by step 2.
- **Mathlib lemmas needed**: `tendsto_tsum_of_dominated_convergence`, `Polynomial.eval_finset_sum`,
  `PowerSeries.evalT` unfolding, `Polynomial.hasseDeriv_pow`-type (or direct binomial computation).
- **Sources**: [Bel] Lemma II.2.14 (ii), Prop II.2.15 + proof (`bellaiche.txt` 2529–2542).
- **Generality**: `IsTate R` (for the entireness bound).
- **Progress** (2026-09-06T03:05Z): DONE, sorry-free, std axioms. Route exactly as sketched. New public
  API: `PowerSeries.exists_forall_norm_coeff_le_of_eq_mul_add` (Entire.lean, division section: for
  monic `B` a radius `c ≥ 1` with `‖coeff k r‖ ≤ M` whenever `F = Bq + r` and `‖coeff j F‖ c^j ≤ M`
  for all `j` — Martin's `norm_eq_max_of_eq_mul_add_of_isMulDistinguished` at `distRadius B`, which
  stays private), `Coleman.tendsto_eval_one_dPoly` (coefficientwise continuity of `P ↦ D(B,P)_N(1)`
  via `Continuous.matrix_det` on the `evalRingHom 1`-mapped Sylvester matrix — no degree bounds, no
  norms), `Coleman.tendsto_eval_one_dPoly_trunc` (Tannery `tendsto_tsum_of_dominated_convergence` with
  the C3 bound `norm_coeff_dPoly_le_pow` uniform in `N`), private `eval_one_eq_tsum`. Polynomial
  division of the truncations uses `%ₘ`/`/ₘ` by the monic `C u⁻¹ * Q` (`modByMonic_add_div`,
  `natDegree_divByMonic`); `S − S_N = Q'(C u q − q_N) + (r − r_N)` feeds the remainder bound with
  `M = ε/2` from `isRestricted_iff'` at radius `c`. II.2.15 is `dSeries_mul` + `dSeries_coe` +
  `dPoly_bQ_self` + `IsGoodZero.of_factor` at `a = b = 1` (no Hasse-derivative computation needed).
  Statement changes: `hS0 : coeff 0 S = 1` DROPPED from `evalT_one_dSeries_bQ_eq_of_eq_mul_add` and
  `isUnit_evalT_one_dSeries_bQ_iff` (unused); kept in `isGoodZero_dSeries_bQ` (for `dSeries_mul`).
  Generalisations of C1/C4 API forced by the remainders (no unit constant term): `dPoly_succ` and
  private `dPoly_eq_of_le` lost `hP0` (proof via `resultant_add_left_deg` padding on both sides + the
  `f = 0` case), hence `tendsto_coeff_dPoly_trunc`, `dSeries_coe`, `norm_coeff_dSeries_sub_le`,
  `IsEntire.dSeries` lost their `coeff 0 = 1` hypotheses; `dSeries_mul` keeps them (for `dPoly_mul`)
  but lost an unused `[IsTate R]` (runLinter). Renamed `Coleman.IsEntire.dSeries` →
  `_root_.PowerSeries.IsEntire.dSeries` (dot notation). New imports: `Mathlib.Analysis.Normed.Group.Tannery`,
  `Mathlib.Topology.Instances.Matrix`. Traps: `add_le_add_right` in this mathlib is `c + a ≤ c + b`
  (use `Nat.add_le_add_right`); `natDegree_C_mul_le _ _` inside `add_le_add_*` leaves the semiring
  metavariable stuck — pass the arguments explicitly; a `have hAB : ∀ᶠ N in atTop, f N = g N` cannot be
  used as `EventuallyEq` (`hAB.symm` fails) — state it as `f =ᶠ[atTop] g`; opaque `obtain ⟨SN, hSN⟩ :
  ∃ SN, ∀ N, SN N = …` beats `set` for sequences of truncations (no let-unfolding surprises).

### [C6] The spectral mapping formula ([Bel] Prop II.2.16)
- **Status**: done (finished 2026-09-06T03:55Z) | **File**: PhD/TateFredholm/Coleman.lean | **Depends on**: C4, C2 | **Parallel**: yes (with C5) | **Type**: lemma
- **Statement**: `IsCompactoid.aeval` (:267), `charPowerSeries_aeval` (:275).
- **Proof sketch** (L-C6):
  1. `IsCompactoid.aeval`: `aeval u B = ∑_{k≥1} b_k • u^k` (`Polynomial.aeval_eq_sum_range`,
     `B.coeff 0 = 0` kills `k = 0`); `IsCompactoid.finset_sum/smul/comp_right` (Riesz.lean:624/647,
     Matrix.lean:550).
  2. Truncations: `S ↦ π_S u` (`truncation`), `IsCompactoid`; `B(π_S u)` is row-supported on `S`
     (rows outside `S` of `π_S u` vanish, and `(π_S u)^k = π_S u (π_S u)^{k−1}`), with `S×S` block
     `aeval A_S B` where `A_S := of (matrixCoeff (π_S u))` (show `matrixCoeff ((π_S u)^k) = (A_S^k)` on
     `S × S` by induction using `matrixCoeff_comp`/`hasSum_matrixCoeff` and vanishing outside `S`).
  3. Finite case: `charPowerSeries (aeval (π_S u) B) = charpolyRev (aeval A_S B)` (`charCoeff_eq_det_coeff`,
     Fredholm.lean:491) `= dPoly B (charpolyRev A_S) |S|` (C2) `= dSeries B (charPowerSeries (π_S u))`
     (`dSeries_coe`, `charpolyRev A_S = charPowerSeries (π_S u)` by `charCoeff_eq_det_coeff` again).
  4. Limits along the directed family of finite sets: `‖(π_S u) − u‖ → 0` (`tendsto_truncation_comp`),
     `‖aeval (π_S u) B − aeval u B‖ → 0` (polynomial in a normed ring: `opNorm_mul_le`, `opNorm_sum_le`),
     coefficientwise `charCoeff (aeval (π_S u) B) n → charCoeff (aeval u B) n` (`norm_charCoeff_sub_le`,
     uniform norm bound `‖π_S u‖ ≤ ‖u‖`), and `charCoeff (π_S u) n → charCoeff u n`; `norm_coeff_dSeries_sub_le`
     (C4) with `C := sup_n ‖charCoeff (π_S u) n‖`-uniform bound (Hadamard: `‖c_n‖ ≤ ‖u‖^n`… use
     `charPowerSeries_isEntire`-derived bounds uniform in `S` via `norm_charCoeff_sub_le` from `c_n(u)`)
     gives `coeff j (dSeries B (charPowerSeries (π_S u))) → coeff j (dSeries B (charPowerSeries u))`;
     uniqueness of limits.
- **Mathlib lemmas needed**: `Polynomial.aeval_eq_sum_range`, `Polynomial.aeval_def`, `Finset.sum`
  norms, `tendsto_nhds_unique`, `Filter.Tendsto.comp` along `atTop` of `Finset I`.
- **Sources**: [Bel] Prop II.2.16 + proof (`bellaiche.txt` 2543–2554).
- **Generality**: `IsTate R`, model space `c(I,R)`.
- **Progress** (2026-09-06T03:55Z): DONE, sorry-free, std axioms. Route as sketched with two
  simplifications: (a) no operator-space topology is used anywhere (the project deliberately has
  no `SeminormedAddCommGroup` instance on `M →L[R] N`) — polynomial continuity is the explicit
  estimate `norm_aeval_sub_aeval_le` (`‖B(x) − B(y)‖ ≤ (∑ ‖b_k‖ k D^k) ‖x − y‖` for `‖x‖,‖y‖ ≤ D`,
  from `‖x^k − y^k‖ ≤ k D^k ‖x − y‖` by induction with `opNorm_mul_le`/`opNorm_pow_le`/
  `TateFredholm.norm_add_le`), fed to `norm_charCoeff_sub_le`; (b) the uniform coefficient bound
  and the sup-in-`k` closeness for `norm_coeff_dSeries_sub_le` both come from Serre's Prop 8
  `eventually_norm_charCoeff_sub_le`, GENERALISED from `ℕ`-sequences to any filter (proof was
  already filter-generic) and applied along `atTop : Filter (Finset I)`. Finite case: private
  `block S w : Matrix S S R`, `block_comp_of_rows` (right factor row-supported), `block_one`,
  `block_pow_of_rows`, `block_aeval_of_rows`, `rows_aeval_of_rows` (needs `B(0) = 0`),
  `charPowerSeries_eq_charpolyRev_of_rows` (`charCoeff_eq_det_coeff` + `rfl`), then
  `Matrix.charpolyRev_aeval` + `dSeries_coe` (`natDegree (charpolyRev A) ≤ card` via
  `reverse_charpoly`). New public upstream API: Fredholm.lean `apply_coord_eq_zero_of_row` (was
  private; `[IsTate R]` and `[DecidableEq J]` dropped), `matrixCoeff_sum` (moved up from BlockOp.lean,
  duplicate deleted there), `matrixCoeff_comp_eq_sum_of_rows`; Riesz.lean `matrixCoeff_one` public.
  `IsCompactoid.aeval` declared as `_root_.TateFredholm.IsCompactoid.aeval` (dot notation).
  Traps: inside `namespace TateFredholm`, `norm_add_le` is the OPERATOR lemma — use
  `_root_.norm_add_le` for `R`-valued norms; `positivity` cannot see operator norms (use
  `opNorm_nonneg`); `squeeze_zero'` needs `(g := …)` explicitly when the bound is given by `simpa`;
  `ContinuousLinearMap.sum_apply`/`smul_apply` are deprecated (use `sum_apply`, or `show`).

### [CLEANUP-C2] /cleanup on PhD/TateFredholm/Coleman.lean (final)
- **Status**: done (finished 2026-09-06T04:30Z) | **Depends on**: C5, C6 | **Type**: cleanup

## Tranche D — [JN] Theorem 2.2.2 (`PhD/TateFredholm/RieszColeman.lean`)
- **Progress** (2026-09-06T04:30Z): inline cleanup done; gates green (lake build Coleman, full lake
  build 3825 jobs, runLinter clean for Coleman/Entire/Riesz/Fredholm-new). Decompositions: `dSeries_mul`
  96→58 lines (helpers `exists_norm_coeff_le_half_pow`, `norm_coeff_le_of_le_half_pow`,
  `tendsto_norm_coeff_of_le_half_pow`, `norm_coeff_mul_le_half_pow`, `norm_coeff_mul_sub_trunc_le`);
  `evalT_one_dSeries_bQ_eq_of_eq_mul_add` 77→35 (remainder convergence extracted as
  `tendsto_coeff_modByMonic_trunc`); `charPowerSeries_aeval` 110→22 (`tendsto_charCoeff_aeval`,
  `tendsto_coeff_dSeries_charPowerSeries`, both for an arbitrary filter, + `opNorm_le_of_norm_sub_le`);
  shared preamble of `IsEntire.dSeries`/`tendsto_eval_one_dPoly_trunc` extracted as `exists_pow_bound`;
  `norm_coeff_trunc_le` generalised to function bounds `b k`. Docstrings added (`bQ_coeff_zero`,
  `natDegree_bQ`); module docstring gained Main definitions/results; 3 over-long lines fixed;
  `omit`s complete. FLAG for CLEANUP-FINAL: file is ~1500 lines (>1000) — candidate `/split-file`
  into `Coleman/{DPoly,DSeries,SpectralMapping}.lean` once the D-tranche API use is settled.

### [D1] The Riesz–Coleman projector (existence)
- **Status**: done (finished 2026-09-06T05:20Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: C5, C6, D2 (steps 1–2) | **Parallel**: yes (with D2, D3) | **Type**: theorem
- **Statement**: `exists_rieszColemanProjection` (:53).
- **Proof sketch** (L-D1): case `Q.natDegree = 0` (then `Q = 1`, `Q.reverse = 1`; take `p = 1`,
  `w = 1`).  Otherwise `φ' := aeval u (bQ Q v)`, compactoid (C6, `bQ_coeff_zero`);
  `charPowerSeries φ' = dSeries (bQ Q v) (charPowerSeries u) = dSeries (bQ) (Q·S)` (C6, `hF`);
  `IsGoodZero … 1 n` (C5) unfolds to `exists_rieszProjection`'s `h0`/`hunit` at `a = 1`;
  obtain `p, w'`; `1 − 1 • φ' = v⁻¹ • aeval u Q.reverse` (`Polynomial.aeval` of `1 − C v⁻¹ * Q.reverse`);
  so `(1 − φ')^n (1 − p) = 0 ⇒ (aeval u Q.reverse)^n (1 − p) = 0` (multiply by `v^n`), and
  `(1 − φ') w' = p ⇒ aeval u Q.reverse * (v⁻¹ • w') = p`; commutation of `w := v⁻¹ • w'` from `w'`'s.
- **Mathlib lemmas needed**: `Polynomial.aeval_one`, `aeval_sub`, `aeval_C`, `aeval_mul`,
  `Algebra.smul_def`, `smul_mul_assoc`, `mul_pow`-with-commuting-scalars.
- **Sources**: [Bel] Thm II.2.18 + proof (`bellaiche.txt` 2601–2611); [Buz07] Thm 3.3 (`buzzard.txt` 860–870).
- **Generality**: Banach–Tate `R`, no Noetherian hypothesis; `c(I, R)`.
- **Progress** (2026-09-06T05:20Z): DONE, sorry-free, std axioms. GAP in the sketch: `u * p = p * u`
  and `u * w = w * u` do NOT follow from `exists_rieszProjection` applied to `φ' = aeval u (bQ Q v)`
  (that only gives commutation with `φ'`) — they need the closure-of-`R[u]` strengthening, i.e. D2
  step 1–2. So D2's `exists_rieszProjection_isOpLimit` was done first (in Riesz.lean, see D2) and D1
  uses `IsOpLimitAeval.comp` (polynomials in `φ'` are polynomials in `u`) + `IsOpLimitAeval.commute`.
  The witness is `w := v⁻¹ • w'`; `1 − 1 • φ' = v⁻¹ • aeval u Q.reverse` by
  `bQ`, `map_sub/one/mul`, `aeval_C`, `sub_sub_cancel`, `Algebra.smul_def`; the nilpotency transfers
  by multiplying with `v^n` (`smul_pow`, `Units.mul_inv`). Case `deg Q = 0` (`Q = 1`,
  `reverse 1 = 1` via `← C_1, reverse_C`): `p = w = 1`.

### [D2] Closure of `R[u]`, restriction, finiteness, projectivity (+ Pr.lean refactor)
- **Status**: done (finished 2026-09-06T06:05Z) | **File**: PhD/TateFredholm/RieszColeman.lean, PhD/TateFredholm/Pr.lean, PhD/TateFredholm/Riesz.lean | **Depends on**: none | **Parallel**: yes | **Type**: lemma + refactor
- **Statement**: `exists_rieszProjection_isOpLimit` (:67), `commute_of_isOpLimit_aeval` (:79),
  `IsCompletelyContinuous.restrictRange` (:106), `finite_range_of_one_sub_nilpotent` (:115),
  `projective_range_of_finite` (:125).  Refactor: make `exists_lift_cSpace` (Pr.lean:24) public
  (record in `renames.jsonl`) and drop the unused `[IsNoetherianRing R]` from
  `finite_projective_of_one_sub_compact_nilpotent` (Pr.lean:141; update its docstring and README §8).
- **Proof sketch** (L-D2, L-D3):
  1. `exists_rieszProjection_isOpLimit`: reprove `exists_rieszProjection` (Riesz.lean:1922–1970)
     carrying, for each ingredient `N_h, N_{h−1}, u, e, f, p = e^h`, a witness that it is an
     `IsOpLimit` of `aeval u` of polynomials (`resolventPartialSum u a s n = aeval u (pol n)` —
     write the polynomial explicitly: `∑_{m<n} (m+s choose s) a^m ∑_{k≤m+s} c_k X^{m+s−k}`); products of
     `IsOpLimit`s of polynomials: `‖P_kQ_k − PQ‖ ≤ ‖P_k − P‖‖Q_k‖ + ‖P‖‖Q_k − Q‖` with `‖Q_k‖`
     bounded (convergent), via `IsOpLimit.unique`, `opNorm_mul_le`.  Alternatively strengthen
     `exists_rieszProjection` in place (worker's choice; record).
  2. `commute_of_isOpLimit_aeval`: `aeval u (pol k) * w = w * aeval u (pol k)` (`Polynomial.aeval`
     commutes with anything commuting with `u`: `Commute.aeval_left`); `IsOpLimit.comp_left/right`
     + `IsOpLimit.unique`.
  3. `restrictRange` compactness: given `ε`, a finite-rank `v` with `‖φ − v‖ < ε`; then
     `restrictRange (p ∘ v) p …`-type: the operator `(p.range.subtypeL) ∘ … ∘ codRestrict (p ∘ v)`
     has finite rank (`IsFiniteRank.comp_left/right`) and `‖restrictRange φ − …‖ ≤ ‖p‖‖φ − v‖`.
  4. `finite_range_of_one_sub_nilpotent`: run Pr.lean:141–187's proof on `P := ↥p.range` with
     `u := restrictRange φ p hφp` (`CompleteSpace` from `(p.range)` closed: `IsIdempotentElem`
     ⇒ `range = ker (1 − p)` closed; `IsBoundedSMul.of_norm_smul_le`); `(1 − u)^n = 0` from `hnil`
     via `coe_restrictRange_apply`.
  5. `projective_range_of_finite`: `Module.Finite.exists_fin'` gives `g : (Fin n → R) →ₗ ↥p.range`
     surjective, continuous (`continuous_linearMap_pi`, Pr.lean:113 — make public); lift
     `id` through `g` using `exists_lift_cSpace` for the model space `c(I,R)`: the composite
     `c(I,R) →L ↥p.range` (`codRestrict p`) lifts to `β₀ : c(I,R) →L (Fin n → R)`, then
     `β := β₀ ∘ subtypeL` splits `g` (`Module.Projective.of_split`).
- **Mathlib lemmas needed**: `Commute.aeval_left`, `Module.Finite.exists_fin'`, `Module.Projective.of_split`,
  `ContinuousLinearMap.codRestrict`, `Submodule.subtypeL`, `IsIdempotentElem`, `isClosed_ker`.
- **Sources**: [JN] 2.2.2 ("lie in the closure of R[u]"); [Bel] II.2.17 ("stable by every operator…"),
  Prop II.1.20, Prop II.1.21 (`bellaiche.txt` 2226–2254).
- **Generality**: idempotent form (no `HasPr`).
- **Progress** (2026-09-06T05:20Z): steps 1–2 DONE in **Riesz.lean** (not RieszColeman.lean): new
  `IsOpLimit.smul/mul/pow` (OpLimit section; `mul` via `‖T T' − L L'‖ ≤ ‖T − L‖(‖T' − L'‖ + ‖L'‖) +
  ‖L‖‖T' − L'‖`), public `opNorm_smul_le` moved to OperatorNorm.lean (Riesz/Coleman privates
  deleted), new predicate `IsOpLimitAeval u L := ∃ pol, IsOpLimit (fun k ↦ aeval u (pol k)) L` with
  `.aeval/.add/.mul/.smul/.pow/.comp/.of_resolventPartialSum/.commute`, private
  `resolventPoly`/`resolventPartialPoly` (+ `aeval_*` = `resolventCoeff`/`resolventPartialSum`),
  `commute_of_isOpLimit_aeval` (skeleton statement, moved here), and the construction theorem is now
  `exists_rieszProjection_isOpLimit` (conclusion `… ∧ IsOpLimitAeval u p ∧ IsOpLimitAeval u w`) with
  `exists_rieszProjection` a 2-line corollary. The RieszColeman.lean stubs of the same names were
  deleted. Trap: nothing about `c(I, R)`-operators can `omit` ANY of `[IsUltrametricDist R]
  [CompleteSpace R] [NormOneClass R]` (all referenced through the model-space instances); inside a
  theorem named `IsOpLimit.mul`, `h.mul` for `h : IsOpLimit …` resolves to the theorem itself — use
  `Filter.Tendsto.mul h`.
- **Progress** (2026-09-06T06:05Z): steps 3–5 DONE, sorry-free, std axioms. Pr.lean refactor: public
  `exists_lift_cSpace`, `continuous_linearMap_pi`; NEW HasPr-free `finite_of_one_sub_compact_nilpotent
  [CompleteSpace P]` (the old proof body); `finite_projective_of_one_sub_compact_nilpotent` lost
  `[IsNoetherianRing R]` and is a 2-liner (docs in Tate.lean:50/143 still say "Noetherian" — fix in
  CLEANUP-D1). New RieszColeman API: `mem_range_iff_of_idempotent`, `isClosed_range_of_idempotent`
  (`isClosed_eq`), `completeSpace_range_of_idempotent` (`IsClosed.isComplete.completeSpace_coe`),
  `isBoundedSMul_range` (`IsBoundedSMul.of_norm_smul_le` — mathlib has NO `IsBoundedSMul R ↥s`
  instance for submodules; supply it with `haveI`). `restrictRange` compactness: approximant
  `(p.codRestrict p.range _).comp (v.comp p.range.subtypeL)`, bound `‖p‖‖φ − v‖` via
  `opNorm_le_of_forall` + `Submodule.coe_norm`; finiteness = `finite_of_one_sub_compact_nilpotent`
  on `↥p.range` with `(id − restrictRange)^n = 0` by induction on coercions; projectivity =
  `Module.Projective.of_split` with `exists_lift_cSpace` lifting `p.codRestrict` through
  `⟨g, continuous_linearMap_pi g⟩`. Traps: `show ‖(A - B) x‖ ≤ …` with a subtype norm times out
  at whnf (use `rw [Submodule.coe_norm]`); `ContinuousLinearMap.mul_apply`/`one_apply`/`sub_apply`
  are deprecated (use `mul_def` + `comp_apply`, `one_def` + `id_apply`, root `sub_apply`); after
  `ext x` for maps into `↥p.range` the goal is already the coerced equation (no `Subtype.ext`);
  `IsClosed.completeSpace_coe` takes the closedness as an instance — use
  `.isComplete.completeSpace_coe`.

### [D3] Orthogonal multiplicativity and polynomiality
- **Status**: done (finished 2026-09-06T06:40Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: B4 | **Parallel**: yes | **Type**: lemma
- **Statement**: `charPowerSeries_add_of_mul_eq_zero` (:138), `exists_polynomial_charPowerSeries_of_range_le` (:146).
- **Proof sketch** (L-D4):
  1. For every `a : R`: `fredholmDet_mul (hv.smul a) (hw.smul a)` with `a•v * a•w = 0`:
     `fredholmDet (a•(v+w)) = fredholmDet (a•v) · fredholmDet (a•w)`; `fredholmDet_smul`
     (Riesz.lean:1396) rewrites each as `evalT a (charPowerSeries ·)`; so the entire series
     `H := charPowerSeries (v+w) − charPowerSeries v * charPowerSeries w` (entire by
     `charPowerSeries_isEntire`, `IsEntire.mul/sub`) satisfies `evalT a H = 0` for all `a`
     (`IsEntire.evalT_mul/add`); B4's identity theorem at `a = ϖ^k`.
  2. Polynomiality: for `|S| > s.card`, `minor u S = 0`: the columns `u(e_i)`, `i ∈ S`, lie in
     `span s`, so the `S×S` coordinate matrix is `M = A·B` with `A : S × s`, `B : s × S`
     (coordinates of the `u e_i` in terms of `s` — choose via `Submodule.mem_span_finset`);
     pad `A, B` to square matrices with zero columns/rows (`Matrix.fromBlocks`-free: use
     `Matrix.det_mul` on `S × S` after extending the index `s ↪ S`… simplest: `A' := A.submatrix
     id e` zero-extended over an injection `s ↪ S`) ⇒ `det M = det A' · det B' = 0` since `A'` has a
     zero column.  Then `charCoeff u m = 0` for `m > s.card` and `G := ∑_{m ≤ s.card} C (charCoeff u m) X^m`.
- **Mathlib lemmas needed**: `Matrix.det_mul`, `Matrix.det_eq_zero_of_column_eq_zero`,
  `Submodule.mem_span_finset`, `Finset.card_le_card`, `PowerSeries.ext`, `Polynomial.coeff_coe`.
- **Sources**: [Buz07] p. 20 (`buzzard.txt` 690–700), Prop 3.2 proof (`buzzard.txt` 840–842).
- **Generality**: `vw = 0 ∧ wv = 0` (the second may be droppable; keep unless free).
- **Progress** (2026-09-06T06:40Z): DONE, sorry-free, std axioms. `hwv : w * v = 0` DROPPED (unused:
  `fredholmDet_mul` at `a•v, a•w` needs only `a•v * a•w = a•a•(v*w) = 0`); `hu : IsCompactoid u`
  DROPPED from `exists_polynomial_charPowerSeries_of_range_le` (unused: vanishing of all minors of
  size `> card s` is purely algebraic). Multiplicativity exactly as sketched (identity theorem at
  `ϖ^k`). Polynomiality via a new private `det_eq_zero_of_rows_mem_span` (rows in the span of
  `card κ < card ι` vectors ⇒ `det = 0`, by `MultilinearMap.map_sum` + `map_smul_univ` on
  `detRowAlternating` and `AlternatingMap.map_eq_zero_of_not_injective`) applied to the transpose
  of the minor (`Matrix.det_transpose`; columns `u eᵢ|_T` lie in `span s` by
  `Submodule.mem_span_finset`, coordinates via `cSpace.evalCLM`); `G := trunc (card s + 1)`.

### [CLEANUP-D1] /cleanup on PhD/TateFredholm/RieszColeman.lean (after 3rd proof ticket)
- **Status**: done (finished 2026-09-06T07:10Z) | **Depends on**: D1, D2, D3 | **Type**: cleanup
- **Progress** (2026-09-06T07:10Z): inline cleanup of RieszColeman.lean (D1–D3 code): 2 over-long
  lines reflowed; `hminor` extracted from `exists_polynomial_charPowerSeries_of_range_le` as
  private `minor_eq_zero_of_range_le`; shared `one_sub_aeval_bQ` (`1 − aeval u (bQ Q v) = v⁻¹ •
  aeval u Q.reverse`) extracted from D1 and reused by D4; module docstring updated (no longer a
  skeleton; closure-of-`R[u]` data lives in Riesz.lean); Tate.lean overview/table and README
  Noetherian remarks updated for the Noetherian-free Prop II.1.21; Pr.lean `HasPr.exists_lift`
  lost an unused `[IsUltrametricDist N]`. All decls ≤ 45 lines, all public decls documented.

### [D4] Buzzard's Lemma 3.1 (Coleman A4.1), both directions
- **Status**: done (finished 2026-09-06T07:10Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: CLEANUP-D1, C5, C6, B3 | **Parallel**: no | **Type**: lemma
- **Statement**: `isEntireCoprime_iff_isUnit_aeval_reverse` (:165).
- **Proof sketch** (L-D5, reconstructed — flagged): `φ' := aeval u (bQ Q v)`;
  `IsUnit (aeval u Q.reverse) ↔ IsUnit (1 − φ')` (`1 − φ' = v⁻¹ • aeval u Q.reverse`, unit scalar);
  `↔ IsUnit (evalT 1 (charPowerSeries φ'))` (`isUnit_one_sub_smul_iff_isUnit_evalT hu' 1`,
  Riesz.lean:1821, with `1 • φ' = φ'`); `charPowerSeries φ' = dSeries (bQ) (charPowerSeries u)` (C6);
  `↔ IsEntireCoprime Q (charPowerSeries u)` (C5 `isUnit_evalT_one_dSeries_bQ_iff` with
  `charPowerSeries_isEntire`, `charCoeff_zero`).  Degenerate `Q = 1`: both sides true.
- **Mathlib lemmas needed**: `IsUnit.smul_iff`-type (`isUnit_smul_iff` for unit scalars), `one_smul`.
- **Sources**: [Buz07] Lemma 3.1 (`buzzard.txt` 783–786) — proof reconstructed (decomposition L-D5).
- **Generality**: `Q(0) = 1`, unit leading coefficient.
- **Progress** (2026-09-06T07:10Z): DONE, sorry-free, std axioms; a 4-rewrite proof exactly along the
  reconstructed sketch (`isUnit_evalT_one_dSeries_bQ_iff` ← `charPowerSeries_aeval` ←
  `isUnit_one_sub_smul_iff_isUnit_evalT` at `a = 1` ← `one_sub_aeval_bQ`), unit scalar absorbed by
  `Units.isUnit_units_mul` with `Units.map (algebraMap R _).toMonoidHom v⁻¹`. No degenerate case
  split needed.

### [D5] Refinements I: finiteness, projectivity, polynomial `P_N`, `P = P_N P_F`, coprimality of `Q` with `P_F`
- **Status**: done (finished 2026-09-06T07:40Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: D1, D2, D3, D4 | **Parallel**: no | **Type**: lemma
- **Statement**: `IsRieszColemanProjection.finite` (:197), `.projective` (:202), `.exists_polynomial`
  (:208), `.charPowerSeries_eq_mul` (:213), `.isEntireCoprime_range` (:220).
- **Proof sketch** (L-D6 first five children):
  1. `.finite`: D2 `finite_range_of_one_sub_nilpotent` with `φ := aeval u (bQ Q v)` (completely
     continuous: `IsCompactoid.aeval` + `IsCompactoid.isCompletelyContinuous`), `p := 1 − p`
     (idempotent, commutes), `(1 − φ)^n (1−p) = v^{−n}·Q*(u)^n(1−p) = 0` (`h.nil`).
  2. `.projective`: D2 `projective_range_of_finite` with `1 − p`.
  3. `.exists_polynomial`: `range (u(1−p)) ≤ range (1−p) = span (finite generating set)`
     (`Module.Finite.fg_top` gives a finset `s` with `span s = range(1−p)`); D3.
  4. `.charPowerSeries_eq_mul`: `u = u(1−p) + up`, `(u(1−p))(up) = u²(1−p)p = 0` and symmetric
     (`h.comm`, idempotent); D3 multiplicativity; both summands compactoid (`comp_right`).
  5. `.isEntireCoprime_range`: D4 for `ψ := up`: `aeval (up) Q.reverse = v•(1−p) + aeval u Q.reverse * p`
     (expand `(up)^k = u^k p` for `k ≥ 1`, `Q.reverse.coeff 0 = v`); it is a unit with inverse
     `v⁻¹•(1−p) + w*p`… check: `(v(1−p) + Q*(u)p)(v⁻¹(1−p) + wp) = (1−p) + Q*(u)w p = (1−p) + p·p = 1`
     using `h.inv` and commutations.
- **Mathlib lemmas needed**: `Module.Finite.fg_top`, `Submodule.fg_def`, `IsUnit.of_mul_eq_one`.
- **Sources**: [Buz07] Prop 3.2/Thm 3.3 (`buzzard.txt` 830–885).
- **Generality**: via the `IsRieszColemanProjection` record.
- **Progress** (2026-09-06T07:40Z): all five DONE, sorry-free, std axioms, exactly as sketched. New
  public helpers: `one_sub_idem`, `aeval_mul_idem` (`P(up) = P(u)p + P(0)(1 − p)` by
  `Polynomial.induction_on'`, `Commute.mul_pow`, `IsIdempotentElem.pow_succ_eq`); private
  `isUnit_mul_add_smul_one_sub` (block inverse `(Ap + c(1−p))⁻¹ = wp + c⁻¹(1−p)`). `.finite` needs
  `finite_range_of_one_sub_nilpotent (φ := …)` named; `.exists_polynomial` uses `Module.Finite.iff_fg`
  + `u(1−p) = (1−p)u` for the range inclusion; `.isEntireCoprime_range` = D4 at `u := u * p`
  (must be given explicitly: `(u := u * p)`, else the compactoid argument infers `u ∘SL p`).

### [D6] Refinements II: the rank is `deg Q`
- **Status**: done (finished 2026-09-06T10:30Z) | **File**: PhD/TateFredholm/RieszColeman.lean, PhD/TateFredholm/Charpoly.lean (new) | **Depends on**: D5 | **Parallel**: no | **Type**: theorem (the board's hardest single ticket)
- **Statement**: `IsRieszColemanProjection.rankAtStalk` (:230).
- **Proof sketch** (L-D6 `.rankAtStalk`; [Buz07] Prop 3.2's mod-𝔪 argument, run for
  `φ' := aeval u (bQ Q v)` at the linear factor `(1 − T)`):
  1. Trace trick: `N := (1−p).range` finite ⇒ surjection `g : (Fin r → R) →ₗ N`; with
     `a := subtypeL ∘ (g as CLM)` (`c(Fin r, R) ≅ (Fin r → R)` via `finLE`-type equivalence or
     `cSpace` on `Fin r`) and `b := (codRestrict (1−p)) ∘ …` a right inverse-ish: choose `ι : N →L (Fin r → R)`
     splitting `g` (projective: `Module.Projective` gives an `R`-linear section, continuous by
     `continuous_linearMap_pi`-type argument on the finite module — use D2's `exists_lift`); set
     `ψ := ι ∘ (u|_N) ∘ g ∈ End(R^r)` and `ē := ι ∘ g` (idempotent with `range ≅ N`);
     `u'(1−p) = (subtypeL ∘ g) ∘ (ι ∘ codRestrict (u'(1−p)))`-type factorisation so that
     `charPowerSeries (u'(1−p)) = charPowerSeries (ψ' as an operator on c(Fin r, R))` by
     `charPowerSeries_comm` (Fredholm.lean:749), where `u' := φ'`, and the latter is
     `charpolyRev` of the matrix of `ψ'` (`charCoeff_eq_det_coeff` on the full finite index).
  2. Order-`n` good zero at `1` of `charPowerSeries (φ'(1−p))`: `charPowerSeries φ' = dSeries (bQ) (QS)`
     has a good zero of order `n` (C5); `charPowerSeries φ' = charPowerSeries (φ'(1−p)) · charPowerSeries (φ' p)`
     (D3, orthogonality); `evalT 1 (charPowerSeries (φ'p))` is a unit: `1 − φ'p = (1−p) + v⁻¹Q*(u)p`
     is a unit (inverse `(1−p) + v w p`, using `h.inv`), so Serre 11 (`isUnit_evalT_of_isUnit_one_sub_smul`)
     applies; `IsGoodZero.of_mul` (B4).
  3. Reduction modulo a maximal ideal `𝔪` (for a prime `𝔭` use `rankAtStalk` is locally constant?
     — no: prove at every prime directly by localising at `𝔭` and reducing modulo `𝔭R_𝔭`; the
     residue field `κ(𝔭)`): the polynomial identity `charpolyRev ψ' = (1 − X)^n · H'` with `H'` a
     polynomial (`IsGoodZero.exists_factor` for the polynomial `charpolyRev ψ'`, `u = 1`) and
     `H'(1)` a unit; map along `R → κ(𝔭)`: `charpolyRev (ψ'.map _) = (1 − X)^n · H̄'` with
     `H̄'(1) ≠ 0`.
  4. Over the field `κ(𝔭)`: `ψ'.map` is supported on the idempotent `ē.map` (`ψ' ē = ψ' = ē ψ'`),
     and `ē − ψ'` is nilpotent (`(ē − ψ')^n = ι (1 − φ'|_N)^n g = 0` from `h.nil` scaled);
     hence on `range ē.map` (dimension `d := finrank`) the operator is unipotent and on `ker` it
     is `0`: `charpolyRev (ψ'.map) = (1 − X)^d` (`Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`
     on `1 − ψ'|_{range}` over the reduced field; block decomposition `κ^r = range ē ⊕ ker ē`,
     `LinearMap.charpoly` of a direct sum is the product — `LinearMap.charpoly_prodMap`).
  5. Compare `(1 − X)^d = (1 − X)^n H̄'` in `κ(𝔭)[X]` with `H̄'(1) ≠ 0`: `d = n`
     (`Polynomial.rootMultiplicity` at `1`, or cancel `(1−X)^{min}` and evaluate).
  6. `d = Module.rankAtStalk N 𝔭`: `rankAtStalk_eq_finrank_tensorProduct` (FreeLocus.lean:278) and
     `N ⊗ κ(𝔭) ≅ range (ē.map)` (`ē` splits, tensoring preserves the splitting: `range ē ≅ N`
     as `R`-modules via `g, ι`).
- **Mathlib lemmas needed**: `charPowerSeries_comm`, `charCoeff_eq_det_coeff`, `Matrix.charpolyRev`,
  `charpolyRev` commutes with `Matrix.map` along a ring hom (`charpolyRev (M.map f) = (charpolyRev M).map f`; no mathlib
  name found by grep — prove from `RingHom.map_det`, ~10 lines), `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`,
  `LinearMap.charpoly_prodMap`, `Module.rankAtStalk`, `rankAtStalk_eq_finrank_tensorProduct`,
  `Ideal.ResidueField`/`IsLocalRing.ResidueField`, `Polynomial.rootMultiplicity_mul`, `IsUnit.map`.
- **Sources**: [Buz07] Prop 3.2 proof (`buzzard.txt` 843–858): "Reducing the situation modulo a
  maximal ideal of A we see that the reduction of P_N must be a power of the reduction of
  (1−a^{−1}T) … the rank of N at any maximal ideal must equal the degree of P_N modulo this ideal".
- **Generality**: every prime (not only maximal), matching `Module.rankAtStalk`.
- **Progress** (2026-09-06T07:41Z): REPLANNED (basis-free). Sub-tickets, worked in order:
  - D6a `Matrix.charpolyRev_map`: `(M.map f).charpolyRev = M.charpolyRev.map f` (RingHom.map_det).
  - D6b field lemma (`Matrix` over a field `K`): `E * E = E`, `M * E = M`, `E * M = M`,
    `IsNilpotent (E − M)` ⇒ `M.charpolyRev = (1 − X) ^ E.rank`. Proof WITHOUT bases/IsCompl: from a
    basis of `range (toLin' E)` build `P : (Fin d → K) →ₗ (Fin r → K)`, `Q` with `Q P = 1`,
    `P Q = toLin' E`; then `M = P M₁ Q`, `M₁ := Q M P = 1 − K₁` with `K₁ := Q (E − M) P` nilpotent
    (`(Q N P)^k = Q N^k P` since `E N = N E = N`); Sylvester `Matrix.det_one_sub_mul_comm` gives
    `charpolyRev M = det(1 − X M₁) = det((1 − X)•1 + X•K₁)`; the last is `(1 − X)^d` because
    `charpoly (−X•K₁) = Y^d` over the reduced ring `K[X]` (`isNilpotent_charpoly_sub_pow_of_isNilpotent`)
    evaluated at `1 − X`.
  - D6c R-level realisation: `N := (1−p).range`, `g̃ : (Fin r → R) →L N` (from `Module.Finite.exists_fin'`
    + `continuous_linearMap_pi`), continuous section `ι` (`exists_lift_cSpace` as in
    `projective_range_of_finite`), `ψ := restrictRange φ' (1−p)`, `Ψ := toMatrix' (ι ∘ ψ ∘ g̃)`,
    `Ē := toMatrix' (ι ∘ g̃)`; identities `Ē² = Ē`, `ΨĒ = ĒΨ = Ψ`, `(Ē − Ψ)^n = 0`; and
    `charPowerSeries (φ'(1−p)) = ↑(charpolyRev Ψ)` via `charPowerSeries_comm` with
    `toPi : c(Fin r,R) →L (Fin r → R)` (`ContinuousLinearMap.pi evalCLM`), `ofPi := ∑ (proj i).smulRight (single i 1)`
    and `charCoeff_eq_det_coeff` on `Finset.univ` (the operator on `c(Fin r, R)` has rows indexed by
    a finite type, so it is trivially compactoid — take it as the `u` of `charPowerSeries_comm`).
  - D6d rank identification: `rankAtStalk N 𝔭 = Matrix.rank (Ē.map φ)`, `φ = algebraMap R κ(𝔭)`:
    `rankAtStalk_eq_finrank_tensorProduct`, retract `κ ⊗ N ≃ range ((κ⊗ι)∘(κ⊗g̃))`, naturality
    `piScalarRight ∘ baseChange ē = toLin' (Ē.map φ) ∘ piScalarRight` (check on pure tensors),
    `Matrix.rank_eq_finrank_range_toLin`.
  - D6e assembly: good zero of order `n` at `1` of `charPowerSeries (φ'(1−p))` (C5 + D3-type
    orthogonality for `φ'` + Serre 11 for `φ'p`), polynomial factorisation `charpolyRev Ψ = (1−X)^n H'`
    with `H'(1)` unit (`IsGoodZero.exists_factor` + B2 uniqueness), map to `κ(𝔭)`, D6b, compare
    `rootMultiplicity` at `1`.
- **Progress** (2026-09-06T10:30Z): DONE, sorry-free, std axioms, along the replanned route with one
  more simplification: no `rootMultiplicity` — the order of the zero at `1` is read as
  `natTrailingDegree (taylor 1 P)` (`Polynomial.taylor_coeff` + new `PowerSeries.hasseDeriv_coe`
  (Entire.lean) + new `PowerSeries.evalT_coe` (Riesz.lean)), so no power-series factorisation/
  uniqueness is needed at all. New file `PhD/TateFredholm/Charpoly.lean`: `Matrix.charpolyRev_map`,
  `Matrix.charpolyRev_one_sub_of_isNilpotent` (`charpoly` of a nilpotent over the reduced ring
  `K[X]` + `eval_charpoly`), `Matrix.charpolyRev_eq_one_sub_pow_rank` (rank factorisation of the
  idempotent through `Module.finBasis` of `range E.mulVecLin`, `LinearMap.toMatrix'_comp`, Sylvester
  `det_one_sub_mul_comm`). RieszColeman.lean: `toPi`/`ofPi` (`ContinuousLinearMap.pi`/`proj.smulRight
  single`), `isCompactoid_of_finite`, `charPowerSeries_eq_charpolyRev_of_finite`
  (`charCoeff_eq_det_coeff` on `univ` + `det_submatrix_equiv_self`), `matrixCoeff_ofPi_comp_toPi`,
  `exists_retraction_of_finite` (refactored out of `projective_range_of_finite`),
  `restrictRange_one_sub_pow_eq_zero` (out of `finite_range_of_one_sub_nilpotent`),
  `exists_matrix_realisation` (trace property with `u := ofPi ∘ ι ∘ codRestrict (φ p)` into the
  finite model space), `piScalarRight_baseChange` (naturality, by `TensorProduct.induction_on`),
  `rankAtStalk_range_eq_rank` (`Module.rankAtStalk_eq` = residue-field fiber; retract
  `κ ⊗ N ≃ range (J ∘ G)` via `LinearEquiv.ofInjective` + `range_comp_of_range_eq_top`),
  `charPowerSeries_eq_mul_of_comm` (general orthogonal splitting; D5.4 is now an instance),
  `IsRieszColemanProjection.isUnit_evalT_one_aeval_bQ_mul`, `.isGoodZero_aeval_bQ_mul_one_sub`,
  private `natTrailingDegree_eq_of_coeff`, `natTrailingDegree_taylor_one_sub_pow`, `taylor_one_map`,
  `taylor_coeff_of_isGoodZero`. TRAPS: (1) elaborating `charPowerSeries_isEntire A (hu.comp_right w)`
  with `A = φ * w` written as a product hits a 200k-heartbeat `whnf` timeout (the `∘SL` vs `*`
  unification inside a bigger term) — first `have hc : IsCompactoid (φ * w) := hu.comp_right w`, then
  use `hc`; `refine isUnit_mul_add_smul_one_sub … ?_ ?_ ?_ ?_ 1` with holes is similarly slow — pass
  the four facts as `have`s and use `(1 : Rˣ)` coerced in the rewritten target. (2) macOS has NO
  `timeout` command: every `timeout N lake env lean …` exits 127 silently — never wrap with
  `timeout`; use the tool's timeout. (3) failed `lake build`s delete the module's `.olean`, so scratch
  bisections must stub the failing lemma with `sorry` first. (4) `Matrix.map_sub` takes the function
  and a `∀ a b, f (a - b) = …` proof explicitly; `Matrix.mul_sub/sub_mul/mul_assoc/mul_zero` are
  needed for rectangular products (the generic lemmas do not apply to heterogeneous `HMul`).

### [CLEANUP-D2] /cleanup on PhD/TateFredholm/RieszColeman.lean (after 6th proof ticket)
- **Status**: done (finished 2026-09-06T11:20Z) | **Depends on**: D6 | **Type**: cleanup
- **Progress**: inline audit of RieszColeman.lean (D4–D6 code) + Charpoly.lean. `isCompactoid_of_finite`
  lost its unused `[DecidableEq J]` (runLinter finding); `exists_matrix_realisation` (77 lines)
  decomposed into private `toMatrix'_pow` + private `charPowerSeries_mul_eq_charpolyRev_of_retraction`
  (the trace-property computation) + a 47-line assembly; Charpoly's `charpolyRev_eq_one_sub_pow_rank`
  (57 lines) split with the new public `Matrix.exists_mul_eq_of_idempotent` (rank factorisation
  `E = PQ`, `QP = 1`); docstring added to `toPi_ofPi`, stripped from private `taylor_coeff_of_isGoodZero`;
  long line reflowed (`taylor_one_map`). Trap: `ContinuousAdd R` for the monoid structure on
  `(Fin r → R) →L[R] (Fin r → R)` is synthesised through `IsUltrametricDist.nonarchimedeanRing`, so
  `[IsUltrametricDist R]` cannot be omitted even on statements with no norm in them. README/Tate.lean
  overview do not yet list Entire/Resultant/Coleman/RieszColeman/Charpoly — deferred to CLEANUP-FINAL
  as for CLEANUP-B/C. Gates: `lake build PhD.TateFredholm.RieszColeman` (7 D7/D8 sorries only),
  runLinter RieszColeman/Charpoly clean for these files, `#print axioms` standard, full `lake build`.

### [D7] Refinements III: `det(1 − Tu|N) = Q`, `det(1 − Tu|F) = S`, `Q*(u) = 0` on `N`, kernel, invertibility of `u`
- **Status**: done (finished 2026-09-06T13:05Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: CLEANUP-D2, B2 | **Parallel**: no | **Type**: theorem
- **Statement**: `.charPowerSeries_mul_one_sub` (:237), `.charPowerSeries_mul` (:244),
  `.aeval_reverse_mul_one_sub` (:250), `.ker_aeval_reverse` (:256), `.isUnit_mul_one_sub_add` (:262).
- **Proof sketch** (L-D6 remaining children):
  1. `G := charPowerSeries (u(1−p))` polynomial (D5), `H := charPowerSeries (up)`, `Q·S = G·H` (D5),
     `(Q, H) = 1` (D5) ⇒ `G = Q·(aG + bS)` with entire cofactor `K'`; B2 uniqueness: divide `G` by
     `Q` as polynomials (`G = QK + r`, unit leading coefficient) and compare with `G = QK' + 0`:
     `K' = K` polynomial, `r = 0`.
  2. `deg G ≤ n`: localise at each prime `𝔭`: `N_𝔭` free of rank `n` (D6 + `Module.free_of_flat_of_isLocalRing`,
     projective ⇒ flat, `Module.finrank = rankAtStalk`); the trace-trick matrix `ψ` (as in D6 with
     `u` in place of `φ'`) over `R_𝔭` is conjugate to a block matrix `diag(u|_{N_𝔭}, 0)` in a basis
     adapted to `range ē ⊕ ker ē` (both free over the local ring), so `charpolyRev ψ_𝔭 = charpolyRev (u|N_𝔭)`
     has degree `≤ n`; the coefficients of `G` in degrees `> n` map to `0` in every `R_𝔭`
     ⇒ are `0` (`Module.eq_zero_of_localization_maximal` for maximal ideals suffices).
  3. `K` has degree `≤ 0` (`deg(QK) = n + deg K` since `leadingCoeff Q` is a unit — `Polynomial.natDegree_mul'`)
     and `K(0) = G(0)/Q(0) = 1` ⇒ `K = 1` ⇒ `G = Q`.
  4. `H = S`: `Q·S = Q·H` in `R⟦T⟧`; `Q` is a unit there (`PowerSeries.isUnit_iff_constantCoeff`, `Q(0) = 1`).
  5. `Q*(u)(1−p) = 0`: Cayley–Hamilton for the `r × r` matrix `ψ` (`Matrix.aeval_self_charpoly`):
     `charpoly ψ = reflect r (charpolyRev ψ) = reflect r G = X^{r−n} · Q.reverse` (degree `n`,
     `reflect_C_mul_X_pow` termwise), so `ψ^{r−n} Q*(ψ) = 0`; on `N`, `ψ` acts as `u` which is
     invertible there (step 6, proved first) ⇒ `Q*(u)|_N = 0`, i.e. `Q*(u)(1−p) = 0`.
     (Order the proof: 6 before 5.)
  6. `u` invertible on `N`: from `Q*(u)^n(1−p) = 0` (`h.nil`, available before step 5):
     `Q*(u) = v•1 + u·R₁(u)` with `R₁` the polynomial `(Q.reverse − C v)/X`; `(v + uR₁(u))^n (1−p) = 0`
     expands to `v^n (1−p) = u·(stuff)(1−p)` ⇒ `u(1−p)` has a two-sided inverse on `N`:
     `u(1−p) + p` is a unit with inverse `v^{−n}(stuff)(1−p) + p` (all commute with `p`).
  7. `ker Q*(u) = range (1−p)`: `⊇` from 5; `⊆`: `Q*(u)x = 0 ⇒ px = Q*(u)wx = wQ*(u)x = 0`
     (`h.inv`, `h.comm_w`), so `x = (1−p)x`.
- **Mathlib lemmas needed**: `PowerSeries.isUnit_iff_constantCoeff`, `Polynomial.natDegree_mul'`,
  `Polynomial.reflect` lemmas, `Matrix.aeval_self_charpoly`, `Module.free_of_flat_of_isLocalRing`,
  projective ⇒ flat (a mathlib instance; exact name to pin by `lean_loogle` at execution — grep found neither `Module.Flat.of_projective` nor `Module.Projective.flat`), `Module.rankAtStalk_eq_finrank_of_free` (FreeLocus.lean:250), `IsLocalization.map`-compatibility of `charpolyRev` (`RingHom.map_det`),
  `Module.eq_zero_of_localization_maximal`.
- **Sources**: [Buz07] Thm 3.3 proof ("Q divides G. But G and Q have degree n …"); [JN] 2.2.2 proof
  ("Q is not a zero divisor since Q(0) = 1"; "det(u| Ker Q*(u)) = Q*(0) ∈ R^×") (`jn.txt` 675–681).
- **Generality**: as the record.
- **Progress** (2026-09-06): all five proved (std axioms), order 6 → 2 → 1/3 → 4 → 5 → 7 as sketched.
  Statement changes: `exists_matrix_realisation` now quantifies over all `φ` commuting with `p`
  with a *shared* idempotent `E` (`∃ r E g ι, g ∘ ι = 1 ∧ E = toMatrix' (ι ∘ g) ∧ E² = E ∧
  ∀ φ hφp, ∃ Ψ, Ψ = toMatrix' (ι ∘ φ|_N ∘ g) ∧ ΨE = Ψ ∧ EΨ = Ψ ∧ (nilp) ∧ charPowerSeries (φ p) = charpolyRev Ψ`);
  new public `IsRieszColemanProjection.natDegree_le_of_charPowerSeries_eq` (step 2, the degree
  bound) and, in Charpoly.lean, `Matrix.charpolyRev_mul_comm`, `Matrix.charpolyRev_eq_of_mul_eq`
  (Sylvester), `Matrix.natDegree_charpolyRev_le`, `Matrix.mulVecLin_eq_self_of_mem_range`,
  `Matrix.projective_range_mulVecLin_of_idempotent`, `Matrix.exists_mul_eq_of_idempotent`
  generalised to any nontrivial comm ring with free range, `Matrix.charpolyRev_eq_one_sub_pow_of_mul_eq`
  (field, along a given factorisation). Step 2 as executed: the unipotent identity
  `charpolyRev (1 − N) = (1 − X)^card` is FALSE over non-reduced rings (e.g. `ℤ/4`), so the rank at
  `𝔪` is read in the residue field of `R_𝔪` (`IsLocalRing.residue`) while the degree bound is read in
  `R_𝔪` (Sylvester needs no reducedness): `range (E ⊗ R_𝔪)` is free (`Module.free_of_flat_of_isLocalRing`
  + `Module.Projective.of_split` + `Module.Flat.of_projective`), factor `E = PQ`, `QP = 1_m`; over
  `k(𝔪)` the good zero of order `n` of `det(1 − Tφ'|N)` forces `m = n` (D6's Taylor argument,
  extracted as private `eq_of_isGoodZero_of_map_eq`, also used by D6 now); then
  `natDegree (charpolyRev (Ψu ⊗ R_𝔪)) ≤ m = n` and `eq_zero_of_localization` at maximal ideals.
  Step 5: Cayley–Hamilton on the realisation `Ψ = toMatrix' (ι ∘ u|_N ∘ g)`, `charpoly Ψ = Q* · X^(r−n)`
  (private `reflect_reflect'`, `reflect_eq_reverse_mul_X_pow`, `charpoly_eq_of_charpolyRev_eq`),
  transported to `N` by private `aeval_comp_of_comp_eq` (intertwiner `Ψl ∘ ι = ι ∘ ψ`) and
  `coe_aeval_restrictRange_apply`, then `u^(r−n)` cancelled with step 6 via private
  `one_sub_mul_pow_eq : (1 − p)(u(1 − p) + p)^k = u^k (1 − p)`. Step 6 via private
  `exists_mul_aeval_mul_one_sub_eq` (`Q.reverse^n = X·T + C vⁿ` by `Polynomial.X_mul_divX_add`) and
  the existing block-inverse lemma with `p ↦ 1 − p`. Traps: `set m := finrank …` after obtaining
  matrices typed by `Fin (finrank …)` shadows them (hypotheses keep the old `P✝`) — never `set` a
  term occurring in the type of a hypothesis; `rw [hv.mul_right_eq_zero]` cannot see through `≠`
  (use `.not.2`); `Matrix.charpolyRev_map` direction is `(M.map f).charpolyRev = M.charpolyRev.map f`;
  `Module.End.mul_eq_comp/mul_apply/commute_pow_left_of_commute` live in `Module.End`, not
  `LinearMap`; `PowerSeries.eq_mul_add_r_unique` (namespace); `modByMonic_add_div p q` takes `q`
  explicitly with no monic hypothesis; `congrArg (g ∘ₗ ·) h` fails to infer the lambda type.

### [D8] Uniqueness of the complement; slope-decomposition core of [JN] 2.2.13
- **Status**: done (finished 2026-09-06T13:40Z) | **File**: PhD/TateFredholm/RieszColeman.lean | **Depends on**: D7, D4 | **Parallel**: no | **Type**: theorem
- **Statement**: `.eq_range_of_isTopCompl` (:270), `.isUnit_aeval_reverse_of_isEntireCoprime` (:282).
- **Proof sketch**:
  1. Uniqueness ([Bel] II.2.17): let `F'` be as hypothesised.  Show `F' ⊆ range p`: for `x ∈ F'`,
     `(1−p)x ∈ N`; but `(1−p)x = x − px` and `x = Q*(u)y` for `y ∈ F'` (surjectivity on `F'`), so
     `(1−p)x = (1−p)Q*(u)y = Q*(u)(1−p)y = 0` (D7 step 5: `Q*(u)(1−p) = 0`); hence `x = px ∈ range p`.
     Conversely `range p ⊆ F'`: for `z = pz`, decompose `z = n + f` along `N ⊕ F'` (`IsTopCompl`);
     then `n = z − f` and `Q*(u)n = Q*(u)z − Q*(u)f`; `Q*(u)n = 0` (5), so `Q*(u)z = Q*(u)f ∈ F'`;
     also `pz = z`: `z = Q*(u)wz` (`h.inv`), so `z ∈ range Q*(u) ∩ …`; use injectivity of `Q*(u)` on
     `F'` and on `range p` (`Q*(u)w = wQ*(u) = p` on `range p`) to conclude `z ∈ F'`: write
     `z = n + f`, apply `Q*(u)w`: `z = Q*(u)w n + Q*(u)w f`; `Q*(u)wn = wQ*(u)n = 0`… careful — spell
     out: `n = z − f ∈ range p + F'`; `Q*(u) n = 0 ⇒ n ∈ ker Q*(u) = N` (D7 step 7) fine, then
     `f = z − n` with `Q*(u)f = Q*(u)z`; injectivity of `Q*(u)` on `F'` gives `f` unique; and
     `z ∈ range p` with `z − f = n ∈ N ∩ (range p + F')`… conclude via `IsTopCompl` uniqueness of
     decompositions: `z = 0 + z` (in `N ⊕ range p`) and `z = n + f` (in `N ⊕ F'`) — both
     decompositions along `N` with complements `range p`, `F'`; the map `range p → F'`, `z ↦ f`
     is the projection; show `n = 0` by `Q*(u)`-injectivity: `Q*(u)n = 0` and `n ∈ range p + F'`
     where `Q*(u)` is injective on `range p` (`Q*(u)x = 0, x = px ⇒ x = wQ*(u)x = 0`) and on `F'`;
     `n = n₁ + n₂`, `Q*(u)n₁ = −Q*(u)n₂ ∈ Q*(u)(range p) ∩ Q*(u)(F') = range p ∩ F'`… `⊆ range p ∩ F'`
     which is `0`? not known.  Use instead [Bel]'s formulation: `N'' := p(F')`, a submodule on
     which `Q*(u)` is bijective (image of `F'` under `p`, `p` commutes with `Q*(u)`) and nilpotent
     … — the worker should follow [Bel] II.2.17's text: "Consider the closed φ-stable submodule
     N'' = p(N + N'). On N'', φ is nilpotent since it is nilpotent on N + N', and invertible since
     it is invertible on F. Thus N'' = 0 and N = N'." transposed to the complement (`(1−p)(F')`:
     `Q*(u)` invertible on `F'` ⇒ invertible on `(1−p)F'`, and zero on `N ⊇ (1−p)F'` ⇒ `(1−p)F' = 0`
     ⇒ `F' ⊆ range p`; equality by both being complements of `N`: `IsTopCompl` + `Submodule.eq_of_le_of_…`
     via `p(range p) = range p` and the direct-sum count `range p = p(F' ⊕ N) = p(F') ⊆ F'`).
  2. Decomposition core: D4 for `ψ := up` with `charPowerSeries ψ = S` (D7 step 4) and
     `IsEntireCoprime P S` gives `IsUnit (aeval (up) P.reverse)`; `aeval (up) P.reverse =
     (leadingCoeff P)•(1−p) + aeval u P.reverse * p`; a unit iff `aeval u P.reverse * p + (1−p)` is
     (unit scalar on the `N`-part).
- **Mathlib lemmas needed**: `Submodule.IsTopCompl` API (Complement.lean:82–310), `Submodule.map`,
  `LinearMap.range_comp`, `IsUnit.mul_iff` on orthogonal idempotent blocks.
- **Sources**: [Bel] II.2.17 uniqueness (`bellaiche.txt` 2586–2596); [JN] Thm 2.2.13 proof (`jn.txt` 822–829).
- **Generality**: as the record; `P` any multiplicative polynomial coprime to `S`.
- **Progress** (2026-09-06): both proved (std axioms); RieszColeman.lean is sorry-free.
  Statement change: `eq_range_of_isTopCompl` lost the two unnecessary hypotheses `hstab`
  (`u`-stability of `F'`) and `hinj` (injectivity of `Q*(u)` on `F'`): the proof only needs
  `F' ⊆ Q*(u)(F')` — for `x = Q*(u) y`, `(1 − p) x = Q*(u)(1 − p) y = 0` (D7) so `F' ⊆ range p`;
  and a complement of `range (1 − p)` inside `range p` is `range p` (decompose `p z = n + f`,
  apply `p`). No [Bel] II.2.17 nilpotent/invertible argument needed. Part 2 = D4 for `u p`
  (`charPowerSeries (u p) = S` by D7) + `aeval_mul_idem` + private
  `isUnit_mul_add_one_sub_of_isUnit` (`(A p + c(1 − p))(p + c⁻¹(1 − p)) = A p + (1 − p)`).
  Trap: elements of `LinearMap.range ↑(1 − p)` come as `↑(1 − p) n'` (coerced CLM) — rewrite
  `ContinuousLinearMap.coe_coe` before applying `p ((1 − p) n') = 0`.

### [CLEANUP-D3] /cleanup on PhD/TateFredholm/RieszColeman.lean (final)
- **Status**: done (finished 2026-09-06T14:10Z) | **Depends on**: D8 | **Type**: cleanup
- **Progress**: inline audit of the D7/D8 code. Private `reflect_reflect'` replaced by mathlib's
  `Polynomial.reflect_reflect`; the two 60-line proofs split: private `card_eq_of_isGoodZero`
  (residue-field rank count along a factorisation over a local ring) out of
  `natDegree_le_of_charPowerSeries_eq`, private `exists_eq_mul_of_eq_mul_isEntire` (entire
  divisibility ⇒ polynomial divisibility, via `PowerSeries.eq_mul_add_r_unique`) out of
  `charPowerSeries_mul_one_sub`; module docstring gained a "Main results" list; deprecated
  `ContinuousLinearMap.add_apply/zero_apply` replaced. RieszColeman.lean: 1252 lines, sorry-free,
  no line > 100, longest proof 48 lines, runLinter clean for the file, std axioms, full `lake build`
  (3825 jobs). Trap: `set K := …` then `rw [Polynomial.coe_mul]` rewrote inside `↑K` (kabstract
  unfolds let-bound fvars) — use an opaque `obtain ⟨K, hK⟩ : ∃ K, K = … := ⟨_, rfl⟩`.

## Tranche E — the vertex factorisation (`PhD/TateFredholm/SlopeFactor.lean`)

### [E1] Dominance API and the division estimate
- **Status**: done (finished 2026-09-06T14:40Z) | **File**: PhD/TateFredholm/SlopeFactor.lean | **Depends on**: B1 | **Parallel**: yes | **Type**: def + lemma
- **Statement**: `exists_isDominantPoly_of_isUnit_leadingCoeff` (:50), `IsDominantPoly.mul` (:57),
  `norm_coeff_r_mul_pow_le_of_eq_mul_add` (:78).
- **Proof sketch** (L-E1):
  1. [Bel] II.2.5: `ρ₀ := max 1 (max_i ‖a_i‖/‖a_d‖…)`: with `u = leadingCoeff` a unit,
     `‖a_i‖ρ^i ≤ ‖a_d‖ρ^d` for `ρ ≥ ρ₀ := max 1 (max_i ‖a_i‖·‖u⁻¹‖)` since `‖a_d‖ ≥ ‖u⁻¹‖⁻¹`;
     strictness above `d` vacuous.
  2. `.mul`: convert to Martin: a `ρ`-dominant `P` with *multiplicative* leading coefficient is
     `IsMulDistinguished ρ (toRestricted ρ P) (natDegree P)` (attainment + strict domination of
     later terms vacuous); `norm_mul_of_isMulDistinguished` (MulDistinguished.lean:221) gives
     `‖PQ‖_ρ` attained at `deg P + deg Q` with later terms strictly smaller.  If the leading
     coefficient is only a unit, first rescale by it (`IsNormMulUnit` needed: add the hypothesis
     `IsMultiplicative P.leadingCoeff`/`Q.leadingCoeff` to the statement if the proof requires it —
     record as a statement tightening, not a B2; the `A`-instance satisfies it).
  3. Division estimate: `B` dominant with multiplicative leading coefficient ⇒ distinguished at
     radius `ρ`; the division `F = Bq + r` with `q` entire is a Weierstrass division at radius `ρ`
     (uniqueness), so `norm_eq_max_of_eq_mul_add_of_isMulDistinguished` gives `‖r‖_ρ ≤ ‖F‖_ρ ≤ M`
     (`PowerSeries.Restricted.norm_le_iff`, GaussNorm.lean:178).
- **Mathlib lemmas needed**: `Polynomial.norm_toRestricted` (GaussNorm.lean:293), `Finset.sup'`,
  `IsNormMulUnit`, `Restricted.norm_le_iff`.
- **Sources**: [Bel] Def II.2.3–II.2.4, Lemma II.2.5 (`bellaiche.txt` 2369–2388); [JN] Lemma 2.2.9 proof
  (`jn.txt` 773–779); [Bel] Prop II.2.8 estimates (2380–2384).
- **Generality**: radius `ρ > 0` real; multiplicative-unit hypothesis where Martin needs it.
- **Progress** (2026-09-06): all three proved (std axioms). Statement changes: `IsDominantPoly.mul`
  gained `(hm : IsMultiplicative P.leadingCoeff)` — only the FIRST factor needs it (the proof is
  `‖PQ‖_ρ = ‖P‖_ρ‖Q‖_ρ` by Martin's `norm_mul_of_isMulDistinguished` for `P`, plus
  `‖lc P · lc Q‖ = ‖lc P‖‖lc Q‖`); strictness above the degree is vacuous for polynomials. Two new
  public helpers: `norm_toRestricted_of_isDominantIndex` (Gauss norm of a polynomial with dominant
  index `N` is its `N`-th Gauss term; takes `[Fact (0 < ρ)]` since the `Norm` instance on
  `Restricted R ρ` appears in the statement) and `IsDominantPoly.isMulDistinguished` (the bridge
  `IsDominantPoly ρ P` + multiplicative leading coefficient ⇒ `IsMulDistinguished ρ ↑P P.natDegree`).
  `exists_isDominantPoly_of_isUnit_leadingCoeff` takes `ρ₀ = 1 + Σ_{i ≤ deg} ‖a_i‖‖v⁻¹‖` with
  `v` the leading unit, using only `1 ≤ ‖v⁻¹‖‖v‖` (no multiplicativity). The division estimate is
  Martin's `norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished` composed with
  `Restricted.norm_le_iff`.

### [E2] The vertex factorisation ([Bel] Thm II.3.6, existence)
- **Status**: done (finished 2026-09-06T15:30Z) | **File**: PhD/TateFredholm/SlopeFactor.lean | **Depends on**: E1, B2 | **Parallel**: no | **Type**: theorem
- **Statement**: `exists_isDominantFactorization` (:89).
- **Proof sketch** (L-E2; follow `bellaiche.txt` 2994–3062 line by line):
  1. Normalise `a_N` to `1`: replace `F` by `a_N⁻¹ F` (multiplicative unit keeps the dominant
     index and norms exactly); at the end rescale back and normalise `P(0) = 1` as in the source.
  2. `P₁ := ∑_{i≤N} a_iT^i` (monic of degree `N`, `ρ`-dominant); gap `θ := ‖F − P₁‖_ρ / ‖F‖_ρ < 1`
     (strictness of the dominant index for `k > N`, and `‖F‖_ρ = ‖a_N‖ρ^N = ρ^N`).
  3. Iteration: `F = P_n G_n + S_n` (B2, `P_n` monic ⇒ unit leading coefficient), `P_{n+1} := P_n + S_n`;
     invariants (II.3.3) `‖F − P_n‖_ρ ≤ ‖F − P₁‖_ρ`, hence `‖P_n‖_ρ = ‖F‖_ρ` and `P_n` distinguished
     at radius `ρ`; (II.3.7)/(II.3.8) from E1's estimates: `‖S_n‖_ρ ≤ ‖F − P_n‖_ρ`,
     `‖G_n − 1‖_ρ ≤ ‖F − P_n‖_ρ/‖F‖_ρ`; (II.3.12)/(II.3.13): `S_n(G_{n+1} − 1) = P_n(G_n − G_{n+1}) − S_{n+1}`
     is a Weierstrass division so `‖S_{n+1}‖_ρ ≤ ‖S_n‖_ρ‖G_{n+1} − 1‖_ρ ≤ θ‖S_n‖_ρ` and
     `‖G_n − G_{n+1}‖_ρ ≤ θ^n·const` — geometric decay.
  4. Limits in `Restricted R ρ` (complete): `P_n → P_∞` (polynomials of degree `N`, monic — the
     limit is a polynomial: coefficients above `N` are `0` throughout), `G_n → G_∞`, `S_n → 0`;
     `F = P_∞G_∞`; `‖G_∞ − 1‖_ρ ≤ θ < 1` gives `lt_one`; `P_∞` is `ρ`-dominant of degree `N`
     (`‖P_∞‖_ρ = ‖F‖_ρ` attained at `T^N` with coefficient `1`, and strictness for `k > N`
     vacuous).
  5. `G_∞` entire: for `c ≥ ρ`, divide `F` by `P_∞` at radius `c` (`P_∞` monic ⇒ distinguished at
     large radii — need `c ≥ ρ₀(P_∞)`: use B2's division which is entire, and uniqueness at radius
     `ρ` identifies it with `G_∞`).
  6. Final normalisation: `P := P_∞(0)^{−1}P_∞` (invertible since `F(0) = P_∞(0)G_∞(0) = 1`),
     `G := P_∞(0)G_∞`; check the record's fields (`lt_one` unaffected up to the unit `P_∞(0)`, whose
     norm is `1`… note `‖P_∞(0)‖ ≤ ‖P_∞‖_ρ/ρ^0` — argue via `G(0) = 1` and `‖G − 1‖_ρ < 1` from
     `‖G_∞ − 1‖_ρ < 1` and `‖P_∞(0)^{±1}‖ ≤ 1`? `P_∞(0)` is a unit of norm `≤ 1` with inverse of
     norm `≤ 1` only if `‖P_∞(0)‖ = 1`; instead take `θ` small enough or normalise `F(0) = 1`
     from the start by B-hypotheses: `F(0) = 1` and `G_∞(0) = 1 − (small)` is a unit of norm `1`
     (ultrametric), so `P_∞(0) = G_∞(0)^{−1}` has norm `1` ✓).
- **Mathlib lemmas needed**: `cauchySeq_of_le_geometric_two`/`cauchySeq_of_le_geometric`,
  `PowerSeries.Restricted` completeness (`Complete.lean`), `Restricted.norm_le_iff/norm_lt_iff`,
  `Polynomial.toRestricted` API, `tendsto_pow_atTop_nhds_zero_of_lt_one`.
- **Sources**: [Bel] Thm II.3.6 + proof (`bellaiche.txt` 2985–3062); [Ke09] Prop 3.2.2 (decomposition L-E2).
- **Generality**: any ultrametric Banach ring `R` with `NormOneClass`; no `IsTate` needed.
- **Progress** (2026-09-06): proved (std axioms), but by a DIFFERENT route than the sketch: not
  [Bel]'s Newton iteration but **Weierstrass preparation from division** — divide `X^N` by `F`
  (Martin's `weierstrassDivision_exists_of_isMulDistinguished`, available because `F` entire with
  dominant index `N` and `a_N` a multiplicative unit IS Martin-distinguished of order `N` at `ρ`):
  `X^N = F q + r` with `deg r < N`, so `P₀ := X^N − r` is monic of degree `N`, `‖P₀‖_ρ = ρ^N`
  and `↑P₀ = F q`. Divide `F` by `P₀` entirely (B2): `F = P₀ G₀ + r'`; uniqueness of the Weierstrass
  division BY `F` applied to `F = F·1 + 0` and `F = F·(q G₀) + r'` gives `r' = 0`, so `F = P₀ G₀`
  with `G₀` entire. The cofactor's dominant index is `0`: if the greatest achiever `k₀` of `‖G₀‖_ρ`
  were positive then [Mar16, Lemma 1.26(2)] (`norm_coeff_add_mul_of_isMulDistinguished` for the
  distinguished `P₀`) would make `N + k₀` achieve `‖F‖_ρ`, contradicting the strict domination
  above `N`. Normalisation `P := C(G₀(0))·P₀`, `G := C(P₀(0))·G₀` uses `‖P₀(0)‖·‖a_N‖ = 1`
  (`‖P₀(0)‖ = ‖coeff 0 q‖ ≤ ‖q‖ = ‖a_N‖⁻¹` and `≥` from `P₀(0)·G₀(0) = 1`). Statement change:
  `IsDominantFactorization` gained the field `mulLeadingCoeff : IsMultiplicative P.leadingCoeff`
  (JN's "multiplicative polynomial"; needed by E3 and free here — the leading coefficient `G₀(0)`
  is a unit whose inverse has the inverse norm, so Martin's `isNormMulUnit_of_norm_coe_inv_units`
  applies). Two private helpers: `exists_monic_mul_eq_of_isMulDistinguished`,
  `isDominantIndex_zero_of_monic_mul`.

### [E3] Relative primality of the factors (norm-level [JN] Lemma 2.2.7)
- **Status**: done (finished 2026-09-06T15:30Z) | **File**: PhD/TateFredholm/SlopeFactor.lean | **Depends on**: E2, B3 | **Parallel**: no | **Type**: lemma
- **Statement**: `IsDominantFactorization.isEntireCoprime` (:100).
- **Proof sketch** (L-E3, reconstructed — flagged): `G` restricted at radius `ρ`; `‖G − 1‖_ρ < 1`
  (sup of terms `< 1` tending to `0`: `Restricted.norm_lt_iff` + finitely many `< 1` + tail); so `G`
  is a unit of `Restricted R ρ` (`isUnit_of_norm_lt_norm_constantCoeff`, Units.lean:76, with
  `constantCoeff G = 1`); `P` distinguished at radius `ρ` (`ρ`-dominant + unit leading coefficient —
  rescale to monic); Martin's division of `G⁻¹`: `G⁻¹ = P q' + r'`; B2's division `G = Pq + r`;
  `1 = G G⁻¹ = P(…) + r r'`, so `r r' = 1 − P·(entire)`; reduce `r r'` modulo `P` as polynomials:
  `r r' = P c + d` ⇒ `d = 1` by uniqueness of the division of `1` (B2) and then
  `1 = r' G + P(c' )` with entire `c'` ⇒ `IsEntireCoprime P G` (unfold; or B3's
  `isCoprime_of_mul_add_eq_one` + `isEntireCoprime_iff_isCoprime_of_eq_mul_add`).
- **Mathlib lemmas needed**: `Restricted.isUnit_of_norm_lt_norm_constantCoeff`, `Units.val_inv_mul`,
  `Polynomial.modByMonic`/unit rescaling, `Restricted` coercions to `PowerSeries`.
- **Sources**: [JN] Lemma 2.2.7 statement (`jn.txt` 727–730); proof reconstructed (decomposition L-E3).
- **Generality**: norm level; `0 < ρ`.
- **Progress** (2026-09-06): proved (std axioms) along the sketch, with one change: `G` is a unit of
  `Restricted R ρ` by the **Neumann series** (`isUnit_one_sub_of_norm_lt_one`, from `‖1 − G‖_ρ < 1`),
  NOT by `Restricted.isUnit_of_norm_lt_norm_constantCoeff` — that lemma requires `[NormMulClass R]`
  (multiplicative norm on `R`), which a general Banach ring does not have. Then `G⁻¹ = P q + r`
  (Martin division by the distinguished `P`) gives `1 = P(qG) + rG`; the cofactor is made ENTIRE by
  dividing `1 − rG` by `P` entirely (B2) and comparing remainders at radius `ρ` (uniqueness), which
  forces the entire remainder to vanish. Uses the new record field `mulLeadingCoeff`.

### [CLEANUP-E] /cleanup on PhD/TateFredholm/SlopeFactor.lean (3rd proof ticket + final)
- **Status**: done (finished 2026-09-06T16:00Z) | **Depends on**: E3 | **Type**: cleanup
- **Progress**: inline audit. Module docstring: SKELETON marker removed, proof route (Weierstrass
  preparation, not Newton iteration) documented, "Main definitions"/"Main results" lists added.
  Four private helpers extracted so that no proof exceeds 60 lines: `norm_toRestricted_X_pow`,
  `natDegree_X_pow_sub`, `norm_toRestricted_X_pow_sub`, `isDominantPoly_C_mul` (rescaling a monic
  polynomial by a unit keeps dominance). `omit [CompleteSpace R]` added where runLinter flagged
  unused instance arguments. SlopeFactor.lean: 553 lines, sorry-free, longest proof 58 lines, no
  line > 100, runLinter clean, std axioms, full `lake build` (3825 jobs).

## Tranche F — the application over `A` (`PhD/LWX/TateRiesz.lean`)

### [F1] The rescaled transpose `tateOp`: construction, matrix, row bound, compactoidness
- **Status**: done (finished 2026-09-06T16:40Z) | **File**: PhD/LWX/TateRiesz.lean | **Depends on**: A3 | **Parallel**: yes | **Type**: def + lemma
- **Statement**: `UpDatum.tateOp` (:48, data sorry), `matrixCoeff_tateOp` (:53), `norm_matrixCoeff_tateOp_le`
  (:63), `isCompactoid_tateOp` (:69).
- **Proof sketch** (L-F1):
  1. Define the matrix `Mᵀ' a b := (T^((a.2:ℤ) − b.2) : units) * ofInt (D.matrix ω b a)` on
     `(ι × ℕ) × (ι × ℕ)`; entry bound as in decomposition L-F1 (`norm_T_mul`, `norm_ofInt`,
     `UpDatum.norm_matrix_le`): `‖Mᵀ' a b‖ ≤ p^{−(a.2 − a.2/p)}` (two cases on `b.2 ≤ a.2/p`).
  2. Rows are uniformly bounded (`≤ 1`) and each column `a ↦ Mᵀ' a b` tends to `0` cofinitely
     (the bound depends only on `a.2` and `a.2 − a.2/p → ∞`; `ι` finite): build the operator
     as `UpDatum.op` does (UpMatrix.lean:640–712: `opLinear` via `cSpace.ofTendsto` + `mkContinuous`
     with `norm_tsum_row_le`), or via `exists_coeffEquiv` (Matrix.lean:134).  Replace the `by sorry`
     body by the construction; keep the `p ≠ 2` case split convention of `UpDatum.op` (junk `0`
     at `p = 2`).
  3. `matrixCoeff_tateOp`: `tsum_eq_single` as in `UpDatum.matrixCoeff_op` (UpMatrix.lean:705).
  4. `isCompactoid_tateOp`: `rowNorm (tateOp) a ≤ p^{−(a.2 − a.2/p)}` (`Real.iSup_le`), then
     `Tendsto _ cofinite (𝓝 0)` exactly as `hw_upOp` (Halo.lean:98–110) with `Set.Finite.subset`
     of `univ ×ˢ Iio (2B+2)`.
- **Mathlib lemmas needed**: `Units.val_zpow_eq_zpow_val`, `zpow_sub`, `Real.iSup_le`, `Set.Finite.prod`,
  `Filter.eventually_cofinite`, `Nat.div_le_div_left`.
- **Sources**: [LWX] Thm 3.16 proof (`lwx.txt` 1641–1663); [JN] Def 2.1.5 (`jn.txt` 517–521).
- **Generality**: any `UpDatum`, `p ≠ 2` through the halo bound.
- **Progress** (2026-09-06): all four proved (std axioms), built as a row-sum operator exactly like
  `UpDatum.op` (junk `0` at `p = 2`), not via `exists_coeffEquiv`. New public `UpDatum.tateMatrix`
  (the entry `T^{m−n}·M_{(j,n),(i,m)}`), `UpDatum.norm_tateMatrix_le`, `UpDatum.tateOp_apply`;
  private helpers `norm_tateMatrix_le_one`, `tendsto_tateRow_mul`, `norm_tsum_tateRow_le`,
  `tendsto_tsum_tateRow`, `tateOpLinear`. Shared-file side effects: Halo.lean's private `hw_upOp`
  became public `LWX.tendsto_weight_cofinite_atTop`; HaloTate.lean gained
  `norm_T_zpow_mul`/`norm_T_zpow` (`‖T^k f‖ = p^{−k}‖f‖` for k : ℤ, by `Int.induction_on`; the
  ℕ-only `norm_T_mul` did not suffice). The row bound is the two-case computation
  `‖T^{m−n}‖·‖M_{(j,n),(i,m)}‖ ≤ p^{−(m−n)}·p^{−(n−⌊m/p⌋)⁺} ≤ p^{−(m−⌊m/p⌋)}`. Trap: `omit
  [DecidableEq ι]` is impossible for anything mentioning `c(ι × ℕ, ·)` or `matrixCoeff`;
  `zpow_le_one_of_nonpos₀`'s exponent side goal is not a `positivity` goal
  (`neg_nonpos.2 (Int.natCast_nonneg _)`).

### [F2] Minors and the characteristic series of `tateOp`
- **Status**: done (finished 2026-09-06T17:05Z) | **File**: PhD/LWX/TateRiesz.lean | **Depends on**: F1 | **Parallel**: no | **Type**: lemma
- **Statement**: `minor_tateOp` (:75), `charPowerSeries_tateOp` (:82).
- **Proof sketch** (L-F2):
  1. `minor (tateOp) S = det (of fun a b : S ↦ T^{n_a − n_b} ofInt (M b a))`; factor as
     `Δ * (of fun a b ↦ ofInt (M b a)) * Δ⁻¹` with `Δ = diagonal (T^{n_a})` (units);
     `Matrix.det_units_conj` (Determinant/Basic:192); `det_transpose`; `RingHom.map_det` for
     `ofIntRingHom`; `matrixCoeff_op` to identify with `minor (D.op ω) S`.
  2. `charCoeff (tateOp) n = ∑' S, minor (tateOp) S = ∑' S, ofInt (minor (op) S) = ofInt (∑' S, minor (op) S)`
     (`Summable.tsum`-map along the continuous additive `ofIntRingHom` — `norm_ofInt` ⇒ isometry
     ⇒ `Continuous`; `summable_minor_upOp` (Halo.lean:113)); `PowerSeries.ext` + `coeff_map`.
- **Mathlib lemmas needed**: `Matrix.det_units_conj`, `Matrix.det_transpose`, `Matrix.diagonal`,
  `RingHom.map_det`, `ContinuousLinearMap.map_tsum`/`AddMonoidHom.map_tsum` with `Continuous`,
  `PowerSeries.coeff_map`, `Isometry.continuous`.
- **Sources**: [LWX] "So Char(P) = Char(P')" (`lwx.txt` 1662–1663); Thm 3.16 statement (1596–1611).
- **Generality**: as F1.
- **Progress** (2026-09-06): both proved (std axioms) along the sketch. The minor identity is
  `M' = diagonal (T^{n_a}) · (map ofInt M)ᵀ · diagonal (T^{−n_b})` followed by `det_mul`,
  `det_diagonal`, `det_transpose` and `RingHom.map_det`; the cancellation is
  `∏ T^{n_a} · ∏ T^{−n_a} = 1`. `charPowerSeries_tateOp` uses `HasSum.map` along the isometric
  ring hom `ofIntRingHom` (private `continuous_ofInt` via `AddMonoidHomClass.isometry_of_norm`)
  plus `summable_minor_upOp`. Traps: `set` blocks the `rw`s here (the diagonal/entry lambdas must
  stay explicit); the `ᵀ` notation is scoped to `Matrix` (use `Matrix.transpose`);
  `zpow_add` (group form, for the unit `T`) not `zpow_add₀`.

### [F3] The vertex hypothesis: dominant index and multiplicative unit
- **Status**: done (finished 2026-09-06T17:35Z) | **File**: PhD/LWX/TateRiesz.lean | **Depends on**: F2, E1 | **Parallel**: no | **Type**: lemma
- **Statement**: `isDominantIndex_charPowerSeries_tateOp` (:101), `isMultiplicative_charCoeff_tateOp` (:109).
- **Proof sketch** (L-F3): write `t := card ι`, `λ := lwxLambda p t`, `s := λ n − λ (n−1)` (the
  increment `(n−1)/t − (n−1)/(pt)` by `lwxLambda_succ`), `ρ := p^s`.
  1. `‖c_m‖ρ^m ≤ p^{−λ m + s m}` (`norm_charCoeff_upOp_le` + F2 + `norm_ofInt`); at `m = n`
     equality `p^{−λ n + s n}` (`‖T^{λ n}·e‖ = p^{−λ n}`, `norm_T_mul` iterated, `‖e‖ = 1`).
  2. Convexity of `λ`: increments `d_k := k/t − k/(pt)` are nondecreasing in `k`
     (`monotone_sub_div` composed with `k ↦ k/t`, cf. `lwxLambda_eq_sum_comp`); hence for `m < n`,
     `λ n − λ m = ∑_{k=m}^{n−1} d_k ≤ (n−m)·d_{n−1} = (n−m)s`, and for `m > n`,
     `λ m − λ n = ∑_{k=n}^{m−1} d_k ≥ (m−n)·d_n > (m−n)s` since `d_n > d_{n−1} = s` (the vertex
     condition).  Translate to `‖c_m‖ρ^m ≤ ‖c_n‖ρ^n` (and `<` for `m > n`) via `zpow` monotonicity
     in `ℝ` (`zpow_le_zpow_right₀`, `p > 1`).
  3. Multiplicativity: `charCoeff (tateOp) n = ofInt (T^{λ n}·e) = (T : A)^{λ n} · ofInt e`
     (`ofIntRingHom` map_mul/map_pow, `coe_T`); `isMultiplicative_mul`, `isMultiplicative_T` (pow:
     induction), `isMultiplicative_ofInt_of_isUnit`; `IsUnit`: product of units.
- **Mathlib lemmas needed**: `Finset.sum_range_succ`, `Finset.sum_le_card_nsmul`-type bounds
  (`Finset.sum_le_sum`, `Finset.card_range`), `zpow_le_zpow_right₀`, `zpow_lt_zpow_right₀`, `Nat.div_le_div_right`.
- **Sources**: [LWX] Rmk 3.25 (`lwx.txt` 2112–2115), Thm 3.16 (3.16.1), Step II convexity (1880–1883).
- **Generality**: any genuine vertex `n ≥ 1` of `λ`.
- **Progress** (2026-09-06): both proved (std axioms). New public λ-convexity API in `LWX`
  (outside `UpDatum`): `monotone_lwxLambda_increment`, `lwxLambda_sub_le`, `le_lwxLambda_sub`,
  `lwxLambda_exponent_le`, `lwxLambda_exponent_lt` (the last two are the ℤ inequalities
  `−λ(m) + s·m ≤ −λ(n) + s·n`, strict for `m > n` at a vertex, with `s = λ(n) − λ(n−1)`), plus
  `UpDatum.charCoeff_tateOp` and `UpDatum.exists_charCoeff_tateOp_eq`. `n ≥ 1` is derived from the
  vertex condition (at `n = 0` it reads `x < x`). New shared lemma `TateFredholm.IsMultiplicative.pow`
  in Tate.lean. Traps: `rw [← smul_eq_mul]` before `Finset.sum_le_card_nsmul` rewrites the WRONG
  product (apply the nsmul lemma directly and `rw [Nat.card_Ico, smul_eq_mul]` afterwards);
  ℕ-subtraction inside a `zify` goal needs the inner term made opaque
  (`obtain ⟨c, hc⟩ : ∃ c, c = … := ⟨_, rfl⟩`).

### [CLEANUP-F1] /cleanup on PhD/LWX/TateRiesz.lean (after 3rd proof ticket)
- **Status**: done (finished 2026-09-06T17:40Z) | **Depends on**: F3 | **Type**: cleanup
- **Progress**: the λ-convexity section moved OUT of `namespace UpDatum` (it mentions no `UpDatum`;
  it is now `LWX.*`), `omit [Fintype ι]` added to `norm_tateMatrix_le` (runLinter), module docstring
  de-SKELETONised with "Main definitions"/"Main results". TateRiesz.lean: 514 lines, no long lines,
  longest proof < 45 lines, runLinter clean, `lake build PhD.LWX.TateRiesz` OK (4 F3b/F4 sorries
  remain).

### [F3b] The bridge from [LWX]'s unit-coefficient statement to `IsHaloVertex`
- **Status**: done (finished 2026-09-06T18:10Z) | **File**: PhD/LWX/TateRiesz.lean | **Depends on**: CLEANUP-F1 | **Parallel**: yes (with the D-tranche) | **Type**: lemma
- **Statement**: `HaloInt.isUnit_of_isUnit_coeff_zero` (:144), `UpDatum.isHaloVertex_of_isUnit_coeff` (:153).
- **Proof sketch** (decomposition L-F3b):
  1. Units of `HaloInt`: WLOG `g 0 = 1` (divide by the unit constant); write `g = 1 − x` with `x 0 = 0`.
     Claim: `y := ∑ₖ xᵏ` converges *coefficientwise `p`-adically* and lies in `HaloInt`.  Indeed
     `x = x₊ + x₋` (indices `> 0` / `< 0`), `x₊ ∈ (T)`, `x₋ ∈ (pT⁻¹)` (coefficients `p^{|j|}u_j`), and
     the coefficient of `T^j` in `xᵏ` has valuation `≥ (k − |j|)/2` (each monomial `T^a(pT⁻¹)^b`,
     `a + b = k`, sits at index `a − b` with valuation `b`), so for fixed `j` the sums `∑ₖ (xᵏ)_j`
     converge in `ℤ_p`; the limit stream satisfies the halo bound (each `xᵏ` does); and
     `(1 − x)·y = 1` coefficientwise: the convolution's `j`-th coefficient of `(1 − x)·(∑_{k≤K} xᵏ)`
     is `δ_{j0} − (x^{K+1})_j`, whose valuation `→ ∞`; the convolution commutes with the
     coefficientwise limit because for each fixed `j` only indices `i` with `|i|, |j − i| ≤ K'`
     contribute `p`-adically small terms uniformly (`norm_mul_coeff_le`-type bounds — set up a
     lemma "coefficientwise `p`-adic limits commute with convolution under a uniform halo bound").
     Alternative if the analysis is painful: prove `IsUnit` via the two quotients
     `HaloInt → ℤ_p⟦T⟧/(p)`-style residue maps only if a local-ring structure is available — it is
     not (`pT⁻¹` is a non-unit outside `(T)`), so prefer the convergence argument.
  2. Bridge: `exists_charCoeff_upOp_eq_T_pow_mul` (Halo.lean:137) with `norm_charCoeff_upOp_le`
     gives `c_n = T^{λ(n)} * g`; `g 0 = c_n (λ(n))` by `coeff_T_pow_mul` (HaloRing.lean:461), a unit
     by `hb`; step 1 gives `e : (HaloInt p)ˣ` with `↑e = g`; `‖e‖ = 1` from `‖e‖ ≤ 1`,
     `‖e⁻¹‖ ≤ 1` and `1 = ‖e e⁻¹‖ ≤ ‖e‖‖e⁻¹‖`; the vertex condition is `hvert`.
- **Mathlib lemmas needed**: `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`-type valuation bounds,
  `tendsto_nhds` in `ℤ_[p]`, `IsUnit.mk`/`Units.mk`, `HaloInt.norm_le_one`.
- **Sources**: [LWX] Lemma 3.15 (`lwx.txt` 1591–1595), Cor 3.18 (1681–1697, "with equality holding
  if and only if `b_{n,λ(n)} ∈ ℤ_p^×`"), Step II (1884–1911), Rmk 3.25 (2112–2115).
- **Generality**: the units lemma is about `HaloInt` alone (reusable by the Atkin–Lehner board).
- **Progress** (2026-09-06): both proved (std axioms). The units lemma went through the promised
  coefficientwise geometric series, with a clean invariant that avoids all index bookkeeping:
  for `x` with `x 0 = 0`, `‖(xᵏ)_j‖ ≤ √(p^{j−k})` — the square root turns the "at least `(k−j)/2`
  factors of negative degree" count into a product of two square roots, so the induction step is
  `√(p^{i−k})·√(p^{j−i−1}) = √(p^{j−k−1})`. Hence per-coefficient summability in `ℤ_p`, the
  element `geomInv` (private) with the halo bound inherited from the partial sums, and
  `(1 − x)·geomInv = 1` from `(1 − x)·S_K = 1 − x^{K+1}` (`mul_neg_geom_sum`) plus the uniform tail
  bound `‖(y − S_K)_m‖ ≤ √(p^{m−K−1})` (`Summable.sum_add_tsum_nat_add`) convolved against the halo
  bound of `1 − x`. New public API: `LWX.HaloInt.isUnit_one_sub_of_coeff_zero` and
  `HaloInt.tendsto_mul_coeff_cofinite` made public in HaloRing.lean. The bridge is
  `exists_charCoeff_upOp_eq_T_pow_mul` + `coeff_T_pow_mul` (so `g 0 = c_n(λ(n))`) + the units lemma,
  with `‖e‖ = 1` from `1 = ‖e·e⁻¹‖ ≤ ‖e‖‖e⁻¹‖ ≤ ‖e‖ ≤ 1`. Traps: `le_of_tendsto_of_tendsto` needs
  the filter pinned (`(b := (Filter.atTop : Filter ℕ))`) when one side is constant;
  `Units.mul_inv` does not fire under `norm_mul_le`'s coercions (use `show … = 1 from e.mul_inv`);
  inside `namespace LWX` `norm_add_le` is ambiguous with `TateFredholm.norm_add_le`.

### [CLEANUP-ALL-1] /cleanup-all on the project so far (pre-milestone)
- **Status**: done (finished 2026-09-06T18:30Z) | **Depends on**: CLEANUP-A, CLEANUP-B2, CLEANUP-R, CLEANUP-C2, CLEANUP-D3, CLEANUP-E, CLEANUP-F1 | **Type**: cleanup

### [F4] MILESTONE — [LWX] Rmk 3.25 (one vertex) and [JN] 2.2.2 for the halo `U_p`
- **Status**: done (finished 2026-09-06T18:05Z) | **File**: PhD/LWX/TateRiesz.lean | **Depends on**: CLEANUP-ALL-1, D1, E2, E3, F3, F3b | **Parallel**: no | **Type**: theorem (assembly)
- **Conditional on**: `IsHaloVertex D ω n` — the Atkin–Lehner/classicality input (plan.md "Decision 5"); F3b makes the
  hypothesis exactly [LWX] Cor 3.18's `b_{n,λ(n)} ∈ ℤ_p^×` at a vertex of `λ`.
- **Statement**: `exists_isDominantFactorization_tateOp` (:118), `exists_rieszColemanProjection_tateOp` (:130).
- **Proof sketch** (L-F4, one-line assemblies):
  1. `exists_isDominantFactorization` (E2) with `hF := charPowerSeries_isEntire _ (isCompactoid_tateOp)`,
     `hF0 := charCoeff_zero`-derived, `hN := isDominantIndex_… (F3)`, `hunit, hmul := isMultiplicative_charCoeff_tateOp (F3)`,
     `hρ` positivity of `p^s`.
  2. From (1): `P, G`; `v := IsUnit.unit (dominant.2)`; `IsEntireCoprime P G` (E3);
     `exists_rieszColemanProjection` (D1) with `hF := h.eq`, `hS := h.entire`, `hS0 := h.coeff_zero_G`,
     `hQ0 := h.coeff_zero`; package the record `IsRieszColemanProjection` (`⟨…⟩`), `P.natDegree = n` from `h.natDegree`.
- **Mathlib lemmas needed**: none new.
- **Sources**: [LWX] Rmk 3.25; [JN] Thm 2.2.2; `lwx-halo/plan.md` §"Future board 2".
- **Generality**: hypothesis `IsHaloVertex` explicit (its derivation is out of scope).
- **Progress** (2026-09-06): both assemblies proved (std axioms), exactly as sketched — E2 with
  entirety from `charPowerSeries_isEntire ∘ isCompactoid_tateOp` and `charCoeff_zero`, then D1 with
  the record packed from the `IsDominantFactorization` fields plus E3's coprimality. Done BEFORE
  F3b (the milestone does not depend on it: `IsHaloVertex` is a hypothesis). Trap: the dominance
  API speaks of `PowerSeries.coeff n (charPowerSeries u)` while F3 produced `charCoeff u n` —
  `rw [← charPowerSeries_coeff] at hunit hmul` first.

### [CLEANUP-F2] /cleanup on PhD/LWX/TateRiesz.lean (final)
- **Status**: done (finished 2026-09-06T18:30Z) | **Depends on**: F4 | **Type**: cleanup
- **Progress**: the 80-line `one_sub_mul_geomInv` split into private `tendsto_sqrt_zpow_sub`
  and `norm_mul_geomInv_sub_sum_le`; `omit` added where runLinter flagged unused instance
  arguments in TateRiesz.lean and SlopeFactor.lean. TateRiesz.lean: 802 lines, sorry-free,
  no line > 100, longest proof < 45 lines, runLinter reports nothing in the board's files,
  std axioms. Trap: after extracting a lemma whose statement mentions `p` only through
  `(p : ℝ)`, the `Fact p.Prime` instance can no longer be inferred at the call site — pass
  `(p := p)` explicitly.

### [CLEANUP-FINAL] /cleanup-all on the whole project
- **Status**: done (finished 2026-09-06T18:45Z) | **Depends on**: CLEANUP-F2 | **Type**: cleanup
- **Progress**: `PhD/TateFredholm/README.md` — §11 gained a row for the six new modules, §8's
  heading and rows now record that [Bel] Prop II.1.21's finiteness half is Noetherian-free
  (`finite_of_one_sub_compact_nilpotent`), and "Notes for future work" records that the
  ring-level (family) slope theory is DONE (what remains: the Gelfand-spectrum form of the
  slope conditions, [JN] §2.3, `⊗̂`-base change). `PhD/TateFredholm/Tate.lean`'s module map lists
  the six new modules and no longer claims Prop II.1.21 needs Noetherian.
  `.mathlib-quality/lwx-halo/plan.md`'s "Future board 2" now points at this board and records
  what it delivered. Coleman.lean (1469 lines) was NOT split: it is a single coherent development
  (`dPoly`/`dSeries`, the unit criterion, the good zero, the spectral mapping) and under the
  1500-line threshold. Final gates: full `lake build` 3825 jobs green, all board modules
  sorry-free with standard axioms, runLinter reports nothing in any board file.
- Also: update `PhD/TateFredholm/README.md` (§11 new modules: Entire, Resultant, Coleman,
  RieszColeman, SlopeFactor; §8 Noetherian hypothesis dropped; "Notes for future work": the
  ring-level slope theory is now done at the norm level, with the Gelfand-spectrum form and §2.3
  still deferred), `PhD/LWX/` README/docstrings, and `lwx-halo/tickets.md`'s "Future board 2"
  pointer → this board.

---

## Cleanup-cadence check
Proof/def tickets per file: HaloTate 3 (CLEANUP-A after A3 = 3rd + final), Entire 4
(CLEANUP-B1 after B3, CLEANUP-B2 final), Resultant 1 (CLEANUP-R final), Coleman 6 (CLEANUP-C1
after C3, CLEANUP-C2 final — C6 is the 6th, cleanup follows), RieszColeman 8 (CLEANUP-D1 after
D3, CLEANUP-D2 after D6, CLEANUP-D3 final), SlopeFactor 3 (CLEANUP-E), TateRiesz 5 (CLEANUP-F1
after F3, then F3b, F4, CLEANUP-F2 final); CLEANUP-ALL-1 before the milestone F4; CLEANUP-FINAL last.
`⌈34/3⌉ = 12 ≤ 13` cleanup tickets ✓.
