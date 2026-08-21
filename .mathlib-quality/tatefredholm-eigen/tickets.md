# Ticket Board — TateFredholm/Riesz (zeros of the char. power series are eigenvalues)

**Board path**: `.mathlib-quality/tatefredholm-eigen/` — name it in every beastmode
invocation. Default board = NewtonPolygon agent (hands off); `qmf/`, `jacobs/` taken.
**File**: only `PhD/TateFredholm/Riesz.lean` (skeleton in place, compiles, sorries
only). Never edit other TateFredholm files (NP agent may be touching them); if a
private helper there is needed, restate it locally in Riesz.lean. *(One documented
exception, 2026-08-05: a 6-line duplicate deletion in `Fredholm.lean` forced by a
name collision another board introduced in `Matrix.lean` — see the Summary.)*
**Sources**: quotes + attack logs in `decomposition.md` (this directory). Serre page
numbers are journal pages of Publ. Math. IHÉS 12 (1962).

## Summary
- Total: 42 tickets (30 proof/def + 12 cleanup)
- Open: 0 | In Progress: 10 (all cleanup) | Done: 32 (T001–T030 + CLEANUP-1, CLEANUP-2)
- **CONSOLIDATED CLEANUP RUN (2026-08-05, in progress)** — the 10 remaining cleanup tickets
  (CLEANUP-3..9, ALL-1, ALL-2, FINAL) are all `/cleanup` on the same file, so they are being
  discharged as ONE full-file `/cleanup` pass rather than ten partial ones. Structure:
  * **Phase 0–3 (file-level) DONE**: imports reordered (Mathlib group first, then `PhD.*`,
    alphabetical within groups, blank line between); the one `/-! ### Coordinate machinery …`
    subsection divider at L3024 stripped; **11 `haveI`/`letI` → `have`/`let`** (Lean-3 holdover,
    always a defect per the cleanup rules). Build green after each. No `λ`, no `$`, no
    `push_neg`, no `erw`, no TODO/FIXME in the file to begin with.
  * **A.5 FLAG**: the file is 3620 lines — over the 1000-line bar, so it wants `/split-file`.
    Recorded as a follow-up, not done here (out of `/cleanup` scope).
  * **Phase 4 (per-declaration) IN PROGRESS — 67 of 105 done**: 166 declarations total, of which 41
    were already covered by CLEANUP-1/2, leaving 105. One worker each, dispatched in parallel
    batches chosen to be NON-ADJACENT in the file so their `Edit` surfaces cannot collide (the
    skill's sequential rule exists to prevent edit races; non-adjacency plus name-based location
    plus `Edit`-never-`Write` achieves the same guarantee at 20× throughput). Every worker wrote a
    full audit trail to the session scratchpad `reports/<decl>.md`; no gate failures and no
    phase-checklist gaps in any of them.
  * **PAUSED 2026-08-05 by an external API session limit** (resets 17:00 Europe/London). All 15
    then-in-flight workers died mid-run. **The file was verified GREEN after the deaths** — 3127
    lines, 0 sorries, `lake build` clean; the workers use `Edit` with unique anchors, so nothing
    was left half-applied. The 15 affected declarations are listed in the scratchpad's
    `died_unfinished.txt` and have been returned to the queue.
  * **Phase 5a file-wide sweeps DONE** (the main agent did these while no workers were editing,
    which is the only safe moment for them): `omega` → `lia` (21 sites); `fun x => ` → `fun x ↦ `
    (389 sites, all 35 `match` arrows correctly preserved, dry-run on a copy first); line packing
    (0 lines now exceed 100 codepoints). Each verified by a clean build.
  * **Phase 5b rename pass DONE**: `evalT_zero` → `evalT_zero_eq_coeff_zero` (the old name read as
    `evalT a 0 = 0`, i.e. the `map_zero` lemma, rather than evaluation *at* zero); one call site;
    `.mathlib-quality/renames.jsonl` drained to empty.
  * **Headline structural results so far** — every oversized proof was decomposed, not just golfed:
    `charPowerSeries_eq_pow_mul_of_riesz` 228→52 body lines (7 helpers);
    `eventually_norm_charCoeff_sub_le` 120→47 (3); `charPowerSeries_blockTriangular` (Serre Lemme 2)
    93→7 (4); `exists_rieszProjection` 93→43 (2); `finite_ker_one_sub_smul_pow` 88→39 (5);
    `norm_det_sub_det_le'` 96→42 (2); `norm_coeff_det_le` 75→23 (2, generalised to `[CommRing S]`);
    `matrixCoeff_resolventCoeff_of_rows` 71→45 (3). File 3620 → 3127 lines overall.
  * `#print axioms TateFredholm.exists_riesz_decomposition` re-verified mid-run: still
    `[propext, Classical.choice, Quot.sound]`. MILESTONE-2 survives the cleanup.
  * **TOOLING TRAP for future runs**: the `mcp__lean-lsp__*` tools were NOT connected in this
    session, for the main agent or any subagent. The first worker burned 25 minutes on a 7-line
    lemma hunting for them. Substitutes, which every worker is now told up front:
    `lake build PhD.TateFredholm.Riesz 2>&1 | grep 'Riesz.lean.*error'` for diagnostics;
    `grep -rn <name> .lake/packages/mathlib/Mathlib/` for mathlib search; the vendored
    `.lake/packages/LeanSearchClient` for `#loogle`/`#leansearch` under `lake env lean`.
  * Worker prompt template lives in the session scratchpad (`worker_template.md`).
- Riesz.lean: **0 errors, 0 sorries** (2026-08-05) — was 39 at the start of the T007–T009
  batch, 33 at T010, 31 at T011/T012, 27 at T013–T015, 23 at T016–T018, 18 at T019/T027,
  15 at T020, 12 at T021–T023, 7 at T024–T026, 3 at T028–T030. All 39 filled declarations
  `#print axioms`-clean (propext / Classical.choice / Quot.sound).
- **MILESTONE-2 REACHED (2026-08-05)**: `exists_riesz_decomposition` (Serre 1962 Prop. 12)
  is proved, together with `finrank_ker_one_sub_smul_pow` (`dim N(a) = h`) and the
  block factorisation `charPowerSeries_eq_pow_mul_of_riesz`. Exact axiom output:
  ```
  'TateFredholm.exists_riesz_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TateFredholm.finrank_ker_one_sub_smul_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TateFredholm.exists_eigenvector_of_evalT_charPowerSeries_eq_zero' depends on axioms: [propext,
   Classical.choice, Quot.sound]
  'TateFredholm.charPowerSeries_eq_pow_mul_of_riesz' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- **CROSS-BOARD BREAKAGE + REPAIR (2026-08-05)** — read before the next run. The build was
  red on arrival for two unrelated reasons, neither of them in this board's scope:
  1. A parallel agent (Jacobs board) added a **public** `@[simp] matrixCoeff_sub` to
     `PhD/TateFredholm/Matrix.lean` (uncommitted, to serve `PhD/Jacobs/GenFun.lean:70`).
     That name already existed twice downstream: `private matrixCoeff_sub` in
     `Fredholm.lean:86` and a public duplicate in `Riesz.lean:602`. Result:
     `Fredholm.lean:86:16: a non-private declaration TateFredholm.matrixCoeff_sub has
     already been declared`, and the build never reached Riesz. **Repair**: keep the
     canonical copy in `Matrix.lean` (earliest file, where `matrixCoeff` lives, and the
     one the other board depends on) and delete the two exact duplicates — 6 lines in
     `Fredholm.lean` (a `private` whose two use sites now resolve to the strictly more
     general public lemma) and 3 lines in `Riesz.lean`. No statement changed; `Fredholm`,
     `Riesz` and `PhD.Jacobs.GenFun` all build. This is the one time this board edited a
     file other than `Riesz.lean` — unavoidable, since `Fredholm.lean` compiles first.
  2. `charPowerSeries_eq_pow_of_isNilpotent` (T025's consumer) had regressed: inside its
     `heq` step, `simp only [… Matrix.one_apply]` left the RHS as
     `if (Equiv.subtypeUnivEquiv ⋯) j = (Equiv.subtypeUnivEquiv ⋯) i then 1 else 0`, so the
     follow-up `rw [if_pos rfl, if_pos rfl]` / `rw [if_neg …]` (whose patterns are in terms
     of `↑j = ↑i`) no longer matched. **Repair**: add `heu` (to unfold the `set`-bound `eu`)
     and `Equiv.subtypeUnivEquiv_apply` to the `simp only` list. **Trap for the future**:
     `Equiv.subtypeUnivEquiv` applications are *not* reduced to the subtype coercion by
     `simp only` unless `Equiv.subtypeUnivEquiv_apply` is in the list.
- **Tier 1 of the full Riesz decomposition: DONE (2026-08-04)** — T021
  (`exists_rieszProjection`), T022 (`ker_/range_one_sub_smul_pow_of_rieszProjection`,
  `isTopCompl_range_one_sub_range_of_isIdempotent`), T023 (`rieszProjection_unique`) over a
  general Banach–Tate ring `R`, and T024 (`finite_ker_one_sub_smul_pow`) over a field.
  One new file-scoped private for T021–T023: `apply_of_mul_eq` (reused by T024).
- **Tier-2 groundwork: DONE (2026-08-04)** — T025 (`det_one_sub_X_smul_of_isNilpotent`) and
  T026 (`isCompactoid_of_comp_embedding`, `charPowerSeries_blockTriangular` = Serre's
  Lemme 2). Five new privates, all in `RieszDecomposition` and all index-only: `blockEquiv`,
  `card_blockEquiv`, `fiberEquiv`, `blockCard`, `blockCardFiberEquiv`. Everything T028 needs
  from Q2/Q3 is now available.
- **MILESTONE-1 REACHED (2026-08-04)**: T020 is DONE — a zero of the characteristic power
  series of a compactoid operator over a complete nonarchimedean field IS an eigenvalue
  (Serre 1962 §7 Props. 11–12), together with the iff and the conjugated transport. All
  three `#print axioms`-clean.
- C-cluster: COMPLETE (C0/C1/C2 = T013–T015, `fredholmDet_mul` = T016).
- D-cluster: **COMPLETE — the payoff chain T016 → T017 → T018 → T020 is DONE**. Serre
  Prop. 11 (`isUnit_one_sub_smul_iff_isUnit_evalT`) and the dichotomy
  (`exists_mem_ker_of_hasseDeriv_evalT`) are proved over a general Banach–Tate ring `R`;
  T019 (the field input, `Order`) supplies the order, and T020 assembles the three
  field-level eigenvector theorems (headline / iff / conjugated).
- A-cluster (`PowerSeries.evalT` / `hasseDeriv`) is COMPLETE, `Order` section included
  (T019 + T027 — 2026-08-04).
- Parallel capacity: 4+ (T001/T002/T003/T007 at start; A ⊥ B ⊥ C0; T019 ⊥ B/C/D;
  T025/T026/T027 ⊥ Tier-1)
- EXTENSION 2026-08-04: T021–T030 = Serre's full Riesz decomposition (Prop. 12),
  user-approved. Tier 1 = projectors/decomposition (T021–T024); Tier 2 = dim N = h
  (T025–T029); T030 = assembled Prop. 12 (MILESTONE-2).

Statements below are IN THE SKELETON already — the worker's job is to replace each
`sorry`. Worker preamble for every ticket: the file is inside `namespace TateFredholm`
(or `namespace PowerSeries` for A-cluster tickets); `open Filter Topology` is at the
top; the operator norm on `→L` is `TateFredholm`'s scoped instance (already in scope
inside the namespace).

---

### [T001] IsOpLimit infrastructure
- **Status**: done — **File**: PhD/TateFredholm/Riesz.lean — **Depends on**: none —
  **Parallel**: yes — **Type**: def API (def `IsOpLimit` is already in place)
#### Statement
Fill the sorries of `IsOpLimit.unique`, `IsOpLimit.add`, `IsOpLimit.const`,
`IsOpLimit.comp_left`, `IsOpLimit.comp_right` (section `OpLimit`).
#### Proof sketch
1. `unique`: `‖L − L'‖ ≤ max ‖L − T n‖ ‖T n − L'‖` (or `+` via `norm_add_le`,
   `OperatorNorm.lean:212`) with `opNorm_sub_comm`; squeeze to `‖L − L'‖ ≤ ε` for all
   ε (`le_of_forall_pos_le_add` style), conclude by `opNorm_eq_zero_iff`
   (`OperatorNorm.lean:516`) and `sub_eq_zero`.
2. `add`: `‖(Tn + T'n) − (L + L')‖ = ‖(Tn − L) + (T'n − L')‖ ≤ …` via `norm_add_le`;
   `squeeze_zero` with `Tendsto.add` then `Tendsto.max`? — simplest:
   `squeeze_zero (fun n => opNorm_nonneg _) (fun n => norm_add_le … |>.trans …)`
   against the sum of the two null sequences.
3. `const`: `sub_self` + `opNorm_zero`; `tendsto_const_nhds`.
4. `comp_left/right`: `w * Tn − w * L = w * (Tn − L)` (ring `mul_sub`);
   `opNorm_mul_le` (`OperatorNorm.lean:528`, `[IsTate R]`); `squeeze_zero` against
   `‖w‖ * ‖Tn − L‖` (`Tendsto.const_mul`).
#### Mathlib/repo lemmas
`norm_add_le`, `opNorm_sub_comm`, `opNorm_eq_zero_iff`, `opNorm_mul_le`,
`opNorm_nonneg`, `opNorm_zero` (all TateFredholm.OperatorNorm — signatures verified);
`squeeze_zero`, `Tendsto.const_mul`, `mul_sub`, `sub_eq_zero`.
#### Sources
None (infrastructure; see decomposition O1).
#### Generality
Over `R` Banach–Tate hypotheses of the file; `comp_*` in the `[IsTate R]` part of the
section — exactly as the skeleton's `variable` placement has it.
- **Progress** (2026-08-04, sorry-free, std axioms): `unique` = `‖L−L'‖ ≤ ‖Tn−L‖+‖Tn−L'‖`
  (`abel` rewrite + `norm_add_le` + `opNorm_neg`) squeezed by `ge_of_tendsto'`, then
  `opNorm_eq_zero_iff` + `sub_eq_zero`; `add`/`comp_left`/`comp_right` = `squeeze_zero`
  against `Filter.Tendsto.add`/`.const_mul`/`.mul_const` (dot notation on `IsOpLimit`
  does NOT reach `Filter.Tendsto.*` — spell the namespace out); `const` = `sub_self` +
  `opNorm_zero`. **DEVIATION (signature)**: `[IsTate R]` had to be added to `unique` and
  `add` — `norm_add_le` (`OperatorNorm.lean:212`) and `opNorm_eq_zero_iff` (:516) both
  live in the `[IsTate R]` part of `OperatorNorm.lean`, and without a Tate base both
  statements are in fact FALSE (unbounded continuous maps have `‖·‖ = sInf ∅ = 0`, so a
  constant sequence can have two limits); `const` kept fully general. Also added the
  repo-standard file-level `set_option linter.unusedSectionVars false` (all sibling
  TateFredholm files have it; without it every filled proof warns).

### [T002] Compactoid closure + matrixCoeff arithmetic + product-of-matrices lemma
- **Status**: done — **File**: Riesz.lean — **Depends on**: none — **Parallel**: yes —
  **Type**: lemmas
#### Statement
Fill: `matrixCoeff_add/neg/sub/smul`, `norm_matrixCoeff_le'`, `rowNorm_add_le`,
`rowNorm_neg`, `rowNorm_smul_le`, `IsCompactoid.add/neg/sub/smul` (section
`CompactoidClosure`) and `matrixCoeff_mul_of_rows` (section `DetValue`).
#### Proof sketch
1. `matrixCoeff_*`: unfold `matrixCoeff` (`Matrix.lean:34`, it is
   `u (cSpace.single i 1) j`); `ContinuousLinearMap.add_apply` etc. + the `cSpace`
   FunLike; all `rfl`-adjacent.
2. `norm_matrixCoeff_le'`: `norm_apply_le` (`ModelSpace.lean:57`) then `le_opNorm`
   (`OperatorNorm.lean:136`) with `norm_single_one` (`ModelSpace.lean:119`).
3. `rowNorm_add_le`: `rowNorm = ⨆ i, ‖matrixCoeff …‖`; `Real.iSup_le` with pointwise
   `IsUltrametricDist.norm_add_le_max`; the two `⨆` on the right need `le_ciSup` with
   `BddAbove` from step 2 (`bddAbove_range_norm_of_tendsto_cofinite` is NOT the tool
   here — use the `‖u‖` bound: range ⊆ `Iic ‖u‖`).
4. `rowNorm_neg`: `norm_neg` under the `iSup`. `rowNorm_smul_le`: pointwise
   `norm_mul_le` then `Real.iSup_le` + `mul_le_mul_of_nonneg_left`… (`ciSup` compare:
   `Real.iSup_le` with `le_ciSup_of_le`-free route: bound each term by
   `‖a‖ * rowNorm u j` directly).
5. `IsCompactoid.*`: unfold (`Tendsto (rowNorm ·) cofinite (𝓝 0)`); `squeeze_zero'`
   with `eventually_of_forall` (bounds from 3–4) against `Tendsto.max hu hv` /
   `Tendsto.const_mul` — mind `squeeze_zero` needs `0 ≤ rowNorm` = `rowNorm_nonneg`.
6. `matrixCoeff_mul_of_rows`: `u * v = u.comp v`; expand `v (single i 1)` by
   `hasSum_single` (`ModelSpace.lean:136`) restricted to `S` (coordinates off `S`
   are rows of `v` — wait, `(v (single i 1)) k = matrixCoeff v k i`, zero for
   `k ∉ S` by `hv`), so `v (single i 1) = ∑ k ∈ S, matrixCoeff v k i • single k 1`
   (finite sum; prove by coordinates, `cSpace` ext); apply `u`, `map_sum`,
   `map_smul`, read coordinate `j`.
#### Mathlib/repo lemmas
`IsUltrametricDist.norm_add_le_max` (verify exact name; fallback
`IsUltrametricDist.dist_triangle_max` reformulations), `Real.iSup_le`, `le_ciSup`,
`norm_mul_le`, `rowNorm_nonneg` (`Matrix.lean:368`), `squeeze_zero'`, `Tendsto.max`,
`Tendsto.const_mul`, `hasSum_single`, `norm_single_one`, `le_opNorm`,
`norm_apply_le`.
#### Sources
Serre p. 80 uses closure silently ("v = −au + auv … complètement continu");
decomposition CC1.
#### Generality
`I J` two index types as in the skeleton; `smul`/`neg` without `IsTate`, `add`/`sub`
with (per skeleton variable placement).
- **Progress** (2026-08-04, sorry-free, std axioms): all four `matrixCoeff_*` are plain
  `rfl` (`C₀` add/neg/sub/smul are pointwise, `ContinuousLinearMap.*_apply` are `rfl`);
  `norm_matrixCoeff_le'` = `cSpace.norm_apply_le` + `le_opNorm` + `cSpace.norm_single_one`
  (copy of the private `Matrix.lean:392`); added `private
  bddAbove_range_norm_matrixCoeff` (range ⊆ `Iic ‖u‖`) as the `le_ciSup` witness;
  `rowNorm_add_le` = `Real.iSup_le` + `IsUltrametricDist.norm_add_le_max` (cited name
  RESOLVES as-is) + `max_le_max` + `le_max_of_le_left`; `rowNorm_neg` = `congrArg` +
  `funext` (needs no `BddAbove`); `IsCompactoid.add`/`.smul` = `squeeze_zero` against
  `Filter.Tendsto.max`/`.const_mul`, `.neg` = `Filter.Tendsto.congr`, `.sub` =
  `sub_eq_add_neg` + `.add`/`.neg`; `matrixCoeff_mul_of_rows` = `cSpace.hasSum_single` +
  `hasSum_sum_of_ne_finset_zero` + `HasSum.unique` to get `v (single i 1) = ∑_{k∈S} …`,
  then `map_sum`/`map_smul` pushed through `cSpace.evalCLM j` (`(u*v) x = u (v x)` and
  `evalCLM j f = f j` are both `rfl`). **DEVIATION (signature)**: `[IsTate R]` had to be
  added to `rowNorm_smul_le` and `IsCompactoid.smul` — the planning note "`.smul` needs
  no `IsTate` (pure squeeze)" is wrong: the squeeze needs `‖m_ji‖ ≤ rowNorm u j`, i.e.
  `le_ciSup` with a `BddAbove` witness, and the only witness is the `‖u‖` bound from
  `le_opNorm` (`[IsTate R]`); over a non-Tate base an unbounded row makes `rowNorm = 0`
  and the inequality genuinely fails. `rowNorm_neg`/`IsCompactoid.neg` stay `IsTate`-free
  as planned.

### [T003] PowerSeries.hasseDeriv
- **Status**: done — **File**: Riesz.lean — **Depends on**: none — **Parallel**: yes —
  **Type**: def API
#### Statement
Fill `coeff_hasseDeriv`, `hasseDeriv_zero` (section `HasseDeriv`).
#### Proof sketch
1. `coeff_hasseDeriv`: `PowerSeries.coeff_mk`.
2. `hasseDeriv_zero`: `PowerSeries.ext` + `coeff_mk`; `Nat.choose_zero_right`,
   `Nat.add_zero`, `one_mul`.
#### Mathlib lemmas
`PowerSeries.coeff_mk`, `PowerSeries.ext`, `Nat.choose_zero_right`. Template:
`Polynomial.hasseDeriv_coeff` (`Mathlib/Algebra/Polynomial/HasseDeriv.lean:64`).
#### Sources
Buzzard p. 22 (verbatim quote in decomposition A1).
#### Generality
`[Semiring R]` — maximal; ℕ-cast multiplication.
- **Progress** (2026-08-04, sorry-free, std axioms): `coeff_hasseDeriv := coeff_mk n _`
  (term mode; mathlib's current `PowerSeries.coeff_mk (n) (f)` takes no ring argument);
  `hasseDeriv_zero := PowerSeries.ext fun n => by rw [coeff_hasseDeriv, Nat.add_zero,
  Nat.choose_zero_right, Nat.cast_one, one_mul]`. No lemma-name substitutions; no
  signature change.

### CLEANUP-1 — /cleanup on PhD/TateFredholm/Riesz.lean (scope: sections done so far)
- **Status**: done — **Depends on**: T001, T002, T003 — **Type**: cleanup
- Run `/cleanup` limited to the proved declarations (the file still contains sorries;
  skip file-level "no sorries" gates, golf the finished proofs only).
- **Done 2026-08-04**: HasseDeriv + OpLimit + CompactoidClosure + `matrixCoeff_mul_of_rows`
  golfed 170 → 155 lines (−15): `key`/`hrw` haves folded into their `squeeze_zero`/`rw
  [show … by abel]` sites, `IsOpLimit.const` → `tendsto_const_nhds.congr`, the three
  `rowNorm` lemmas → term mode via `Real.iSup_le`/`iSup_congr` (no `show`/`rw` prelude),
  `IsCompactoid.sub` → `sub_eq_add_neg u v ▸ hu.add hv.neg`. No statement changed;
  0 errors, 39 sorries, `#print axioms` clean.

### [T004] PowerSeries.evalT core
- **Status**: done — **File**: Riesz.lean — **Depends on**: none (parallel with
  T001–T003) — **Type**: def API
#### Statement
Fill `summable_coeff_mul_pow`, `tendsto_norm_coeff_mul_pow_of_isRestricted`,
`evalT_C`, `evalT_one`, `evalT_add` (section `EvalT`).
#### Proof sketch
1. `summable_coeff_mul_pow`: `summable_of_tendsto_cofinite` (`Tate.lean:405`);
   convert the hypothesis via `Nat.cofinite_eq_atTop`; termwise
   `‖coeff n f * aⁿ‖ ≤ ‖coeff n f‖ * ‖a‖ⁿ` (`norm_mul_le` + `norm_pow_le'`?? — in a
   `NormedCommRing`, `‖a ^ n‖ ≤ ‖a‖ ^ n` is `norm_pow_le'` for `0 < n` or via
   `NormOneClass`… careful: section has no `NormOneClass`; use induction lemma
   `norm_pow_le'` variant or add the multiplicative estimate by hand); `squeeze_zero`.
2. `tendsto_…_of_isRestricted`: `isRestricted_iff'` (`ForMathlib
   Restricted/Basic.lean:47`) + monotone comparison `‖a‖ⁿ ≤ cⁿ` (`pow_le_pow_left`,
   norms nonneg) + `squeeze_zero`.
3. `evalT_C`: the family `n ↦ coeff n (C r) * aⁿ` is supported at `0`
   (`PowerSeries.coeff_C`, if-split); `tsum_eq_single 0` + `pow_zero`, `mul_one`.
4. `evalT_one`: `C 1` route (`map_one` of `C`) + 3.
5. `evalT_add`: `map_add` on coefficients + `tsum_add` with the two summabilities
   from 1.
#### Mathlib/repo lemmas
`summable_of_tendsto_cofinite`, `Nat.cofinite_eq_atTop`, `norm_mul_le`,
`pow_le_pow_left`, `tsum_eq_single`, `PowerSeries.coeff_C`, `tsum_add`,
`isRestricted_iff'`, `squeeze_zero`.
#### Sources
Serre p. 76 ("substituer à t n'importe quelle valeur"); decomposition A2/A3.
#### Generality
`[NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]` — no `NormOneClass`, no
Tate. Watch: if `‖aⁿ‖ ≤ ‖a‖ⁿ` genuinely needs `NormOneClass` at `n = 0`
(`‖1‖ ≤ 1`), note `a⁰ = 1` term is handled separately in 3/5 or add the estimate for
`n ≥ 1` + split — resolve at compile time, do NOT add `NormOneClass` to the section
unless forced; if forced, record in the ticket progress note.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change; `NormOneClass`
  NOT needed. The `‖aⁿ‖ ≤ ‖a‖ⁿ` worry is real (`NormedCommRing + IsUltrametricDist` does
  NOT give `‖1‖ ≤ 1`: rescale the `p`-adic norm by 2), but irrelevant for a cofinite/atTop
  limit — new `private tendsto_coeff_mul_pow_cofinite` uses `squeeze_zero_norm'` +
  `filter_upwards [eventually_gt_atTop 0]` so that `norm_pow_le' a hn` (which needs
  `0 < n`) applies, and then `summable_coeff_mul_pow :=
  TateFredholm.summable_of_tendsto_cofinite ·` in term mode.
  `tendsto_norm_coeff_mul_pow_of_isRestricted` = `squeeze_zero` + `isRestricted_iff'`;
  **name substitution: `pow_le_pow_left` → `pow_le_pow_left₀`** (args `(0 ≤ a) (a ≤ b) n`).
  `evalT_C` = `tsum_eq_single 0` (+ `coeff_C` if-split); `evalT_one` =
  `simpa using evalT_C a 1`; `evalT_add` — **`tsum_add` NO LONGER EXISTS as a root name**
  in this mathlib (the summability-filter `L` refactor): use `Summable.tsum_add` /
  `Summable.tsum_sub` by dot notation, i.e.
  `← (summable_coeff_mul_pow hf).tsum_add (summable_coeff_mul_pow hg)`.
  Extra privates added for the rest of the cluster: `evalT_sub'`, `evalT_X`
  (`tsum_eq_single 1`) — `private` is file-scoped, so T012/T019 may use them freely.

### [T005] evalT_mul (Cauchy product)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T004 — **Parallel**: yes —
  **Type**: lemma
#### Statement
`evalT_mul` as in the skeleton.
#### Proof sketch
1. Product summability on `ℕ × ℕ`: for `ε > 0`, the set
   `{p | ε ≤ ‖(coeff p.1 f * a^p.1) * (coeff p.2 g * a^p.2)‖}` is contained in
   `bad_f (ε/B_g) ×ˢ bad_g (ε/B_f)` where `B_•` bound the (null, hence bounded)
   families — `bddAbove_range_norm_of_tendsto_cofinite` (`Tate.lean:424`); both bad
   sets finite (cofinite-null); so the product family is cofinite-null; conclude
   `Summable` by `summable_of_tendsto_cofinite` (on the product type — it applies to
   any index).  Handle `B_• = 0` degeneracies by `le_max_one`-padding.
2. `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
   (`Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:233`) turns
   `(∑' cₘaᵐ)(∑' dₙaⁿ)` into `∑' n, ∑ (k,l) ∈ antidiagonal n, (cₖaᵏ)(d_l aˡ)`.
3. Rewrite the inner sum: `(cₖaᵏ)(d_l aˡ) = cₖd_l * a^n` over the antidiagonal
   (`mul_mul_mul_comm`, `pow_add`); factor `aⁿ` out of the finite sum
   (`Finset.sum_mul`); recognise `PowerSeries.coeff_mul` : `coeff n (f*g) = Σ_{antidiagonal}`.
#### Mathlib/repo lemmas
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` (verified), `PowerSeries.coeff_mul`,
`bddAbove_range_norm_of_tendsto_cofinite`, `summable_of_tendsto_cofinite`,
`Finset.Nat.mem_antidiagonal`, `pow_add`, `Finset.sum_mul`.
DO NOT use the `tsum_mul_tsum_of_summable_norm` family (norm-summability is false
ultrametrically) nor `tsum_mul_tsum_of_nonarchimedean` (needs a `NonarchimedeanRing`
instance we have not verified) — decomposition A3, attack (1).
#### Sources
Decomposition A3.
#### Generality
Same section as T004.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change; the sketch's
  route works verbatim, neither forbidden family used. New `private
  summable_mul_of_tendsto_cofinite {ι κ : Type*} {F : ι → R} {G : κ → R}` (stated for the
  section's `R`, arbitrary index types): `B := max (max Bf Bg) 1` from
  `TateFredholm.bddAbove_range_norm_of_tendsto_cofinite` (the `max … 1` is exactly the
  `B = 0` padding the sketch anticipated), `Metric.tendsto_nhds` to turn the goal into an
  `ε`-statement, `Filter.eventually_cofinite` to turn `∀ᶠ … in cofinite` into `.Finite`,
  then `Set.Finite.prod` / `Set.mem_prod` with the two `(ε/B)`-bad sets; the containment
  is a two-branch `by_contra` on `‖F i * G k‖ ≤ ‖F i‖ * B < (ε/B) * B = ε` (and the mirror
  image).  **ELABORATION TRAP (cost a `(deterministic) timeout at whnf`, 200000 hb):**
  applying it needs EXPLICIT `(F := fun n => coeff n f * a ^ n) (G := …)` — Lean cannot
  solve the higher-order pattern `fun x => ?F x.1 * ?G x.2` against the goal. Then
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` + `coeff_mul` + `Finset.sum_mul` +
  per-term `subst`/`pow_add`/`ring`. **Name substitution: `Finset.Nat.mem_antidiagonal` →
  `Finset.mem_antidiagonal`** (the general `HasAntidiagonal` form; that is what
  `PowerSeries.coeff_mul` produces). Also `Set.mem_setOf_eq` is deprecated in this mathlib
  → `Set.mem_ofPred_eq`.

### [T006] Divided-Taylor evaluation at the factored form
- **Status**: done — **File**: Riesz.lean — **Depends on**: T003, T004, T005 —
  **Type**: lemma pair
#### Statement
`evalT_hasseDeriv_pow_mul_of_lt`, `evalT_hasseDeriv_pow_mul_self`.
#### Proof sketch
1. Local lemma (state `private` above them if useful): the affine product rule
   `hasseDeriv k ((1 - C b * X) * f) =
    (1 - C b * X) * hasseDeriv k f - C b * hasseDeriv (k-1) f` for `1 ≤ k` — by
   `PowerSeries.ext`; coefficients: LHS `= χ(n+k)·(coeff (n+k) f − b·coeff (n+k−1) f)`
   via `coeff_mul` against the 2-term factor; RHS matches by Pascal
   (`Nat.choose_succ_succ'`-type identities). Also the `k = 0` case (`hasseDeriv_zero`).
2. `_of_lt`: induction on `h` (generalising `s`): peel one factor with 1; evaluate:
   both summands contain `hasseDeriv (≤ s) ((1−bX)^{h−1} g)`-type terms with
   `s − 1 < h − 1` and a `(1−bX)`-prefactor whose evaluation is
   `evalT_mul` + `evalT a (1 − C b * X) = 1 − b·a = 0` (T004/T005 pieces:
   `evalT_C`, `evalT`-of-`X` — small inline computation, `tsum_eq_single 1`);
   restrictedness side conditions from `IsRestricted.mul/.pow/.sub/.one/.X/.C`
   (ForMathlib `Restricted/Basic.lean:55–106`, needs `[IsUltrametricDist R]` for
   `.mul` — present).
3. `_self`: same induction; at each step the only surviving term gains a factor
   `−b` from `Δ¹(1−bX) = −C b` evaluated by 1; base `h = 0`: `hasseDeriv 0 = id`.
#### Mathlib/repo lemmas
`PowerSeries.coeff_mul`, `PowerSeries.coeff_X`, `PowerSeries.coeff_C`,
`Nat.choose_succ_succ`, `IsRestricted.mul/.pow/.sub` (+`isRestricted_one/_X/_C`),
`tsum_eq_single`.
#### Sources
Buzzard p. 22 (product rule + factorisation display; verbatim in decomposition A5).
#### Generality
Over `R` with `hba : b * a = 1` (commutative) — strictly more general than the field
use.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change; the two public
  statements are proved from ONE combined private induction
  `evalT_hasseDeriv_pow_mul_aux : ∀ s ≤ h, evalT a (Δˢ (Lʰ·g)) =
  if s = h then (-b)^h * evalT a g else 0` (`L := 1 - C b * X`), induction on `h` with
  `∀ s ≤ h` inside the motive — this merges the sketch's two parallel inductions and makes
  the `_self` case fall out of the same `-b` bookkeeping. Radius: `c := max ‖a‖ 1`, so `hc
  : 0 < c` needs no `a ≠ 0` and `hac : ‖a‖ ≤ c` feeds
  `tendsto_norm_coeff_mul_pow_of_isRestricted`.
  **API-NAME CORRECTION (important for T019 and every later restrictedness side goal):**
  the ForMathlib API is spelled `isRestricted.mul` / `.pow` / `.sub` / `.add` with a
  LOWERCASE `i` and `(c : ℝ)` EXPLICIT and FIRST — `IsRestricted.mul` does not exist and
  dot notation on a hypothesis `hf : IsRestricted c f` does NOT reach them (`IsRestricted`
  is an `abbrev` for `MvPowerSeries.IsRestricted`, which is also lowercase-`i` there).
  Correct usage: `isRestricted.mul c hf hg`, `isRestricted.pow c hL h`,
  `isRestricted.sub c h1 h2`; the nullary ones are `isRestricted_one c`,
  `isRestricted_C c b`, `isRestricted_X c`.
  New privates (all file-scoped, reusable by T012/T019):
  * `evalT_one_sub_C_mul_X : evalT a (1 - C b * X) = 1 - b * a` (via `evalT_sub'`,
    `evalT_mul`, `evalT_C`, `evalT_X`) — with `hba` this is the `= 0` that kills the
    peeled factor.
  * `isRestricted_hasseDeriv (hc : 0 < c) (hf : IsRestricted c f) (k)` — REQUIRED (the
    induction evaluates `evalT` on `Δˢ(Lʰ·g)`, so the sketch's side conditions are not
    enough). Two traps: (a) the binomial factor must be bounded by
    `← nsmul_eq_mul` + `IsUltrametricDist.norm_nsmul_le` (the `to_additive` of
    `IsUltrametricDist.norm_pow_le`) — **do NOT reach for
    `IsUltrametricDist.norm_natCast_le_one`, it requires `NormOneClass`**, which this
    section deliberately lacks; (b) the index shift costs exactly `(c ^ k)⁻¹`:
    `((isRestricted_iff' c f).mp hf).comp (tendsto_add_atTop_nat k) |>.mul_const (c^k)⁻¹`
    with `c^n = c^(n+k) * (c^k)⁻¹` (`mul_inv_cancel_right₀`, needs `c ≠ 0`).
  * `coeff_zero_one_sub_C_mul_X_mul`, `coeff_succ_one_sub_C_mul_X_mul`
    (`sub_mul`/`coeff_C_mul`/`coeff_zero_X_mul`/`coeff_succ_X_mul`), then
    `hasseDeriv_one_sub_C_mul_X_mul (b) (k) (f) : Δ^{k+1}(L·f) = L·Δ^{k+1}f - C b·Δᵏf`
    (stated in `+1` form to dodge `ℕ`-subtraction). **Pascal must be
    `Nat.choose_succ_succ'` (the `n + 1` form) — `Nat.choose_succ_succ` is stated with
    `Nat.succ` and does not `rw`-match.** The `n = 0` branch of the ext still needs the
    SUCC coefficient lemma on the LHS (its index is `0 + (k+1) = k+1`) and the ZERO one on
    the RHS; the `n = j+1` branch needs three `omega` index normalisations
    (`j+1+(k+1) = j+k+1+1`, `j+(k+1) = j+k+1`, `j+1+k = j+k+1`) interleaved with the
    rewrites — `e2` only becomes applicable AFTER `coeff_hasseDeriv` is unfolded. Both
    branches close with `push_cast; ring`.

### CLEANUP-2 — /cleanup on Riesz.lean (A-cluster)
- **Status**: done — **Depends on**: T004, T005, T006 — **Type**: cleanup
- **Done 2026-08-04**: section `EvalT` golfed 257 → 232 lines (−25); biggest win is
  `summable_mul_of_tendsto_cofinite` (−11: the two symmetric `calc` blocks replaced by one
  `hstep : ‖q‖ ≤ B → ‖p‖ < ε/B → ‖p*q‖ < ε` reused via `mul_comm`, `key`/`hcancel` gone).
  `evalT_add`/`evalT_sub'` → term mode (`tsum_congr … |>.trans`), `evalT_one_sub_C_mul_X`
  four `Tendsto` haves → one `hT`, `evalT_C`/`evalT_X` terminal `simp` folded into the `rw`.
  All 10 pinned private helper names kept; 0 errors, 39 sorries, `#print axioms` clean.

### [T007] resolventCoeff and its recursion
- **Status**: done — **File**: Riesz.lean — **Depends on**: none — **Parallel**: yes
  (can start at session 1) — **Type**: def API
#### Statement
Fill `resolventCoeff_zero`, `resolventCoeff_succ`, `resolventCoeff_sub_mul`.
#### Proof sketch
1. `_zero`: `Finset.sum_range_one`, `charCoeff_zero` (`Fredholm.lean:167`),
   `pow_zero`, `one_smul`.
2. `_succ`: `Finset.sum_range_succ'` (peel the TOP index `k = m+1`, whose power is
   `u⁰`) — careful: peel `k = m+1` giving `charCoeff u (m+1) • 1`, and reindex the
   rest: `Σ_{k ≤ m} cₖ u^{m+1−k} = u * Σ_{k ≤ m} cₖ u^{m−k}` via `Finset.mul_sum`,
   `pow_succ'`/`Nat.succ_sub` (needs `k ≤ m` for the exponent shift — inside
   `Finset.sum_congr` with membership), `mul_smul_comm`.
3. `_sub_mul`: rearrange 2 (`eq_sub_of_add_eq'` / `sub_eq_iff_eq_add`).
#### Mathlib/repo lemmas
`Finset.sum_range_succ'`, `Finset.mul_sum`, `mul_smul_comm`, `pow_succ'`,
`Nat.succ_sub`, `charCoeff_zero`.
#### Sources
Serre p. 78 (verbatim in decomposition B1).
#### Generality
No `IsTate`, no compactness — pure algebra (as the skeleton has it).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change; the sketch's route
  works verbatim. `_zero` = `Finset.sum_range_one` + `charCoeff_zero` + **`Nat.sub_self`**
  (needed *before* `pow_zero`: `rw` does not see `0 - 0` as `0`). `_succ` — the sketch's
  "peel the TOP index with `Finset.sum_range_succ'`" is unnecessary and worse: peel with the
  ordinary `Finset.sum_range_succ` (top index `k = m+1`, exponent `m+1-(m+1)`, killed by
  `Nat.sub_self` + `pow_zero`) and prove the reindexing as a separate `have`
  `u * resolventCoeff u m = ∑_{k ∈ range (m+1)} cₖ • u^{m+1-k}` by
  `Finset.mul_sum` + `mul_smul_comm` + `← pow_succ'` + `show m + 1 - k = m - k + 1 by omega`
  (the `k ≤ m` for `omega` comes from `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`);
  **`Nat.succ_sub` is NOT needed** — the `show … by omega` form dodges the `Nat.succ`-vs-`+1`
  rw-matching problem. Close with `exact add_comm _ _`. `_sub_mul` = `resolventCoeff_succ`
  + `add_sub_cancel_right` (one line).

### [T008] Adjugate identification (finite case of Lemme 3)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T002 (for
  `matrixCoeff_mul_of_rows`), T007 — **Type**: lemma pair
#### Statement
`matrixCoeff_resolventCoeff_of_rows`, `matrixCoeff_resolventCoeff_of_notMem`.
#### Proof sketch
1. `_of_notMem`: induction on `m` via `resolventCoeff_succ`; row `j ∉ S` of
   `u * w` vanishes (`matrixCoeff_mul_of_rows`-style expansion with `hS`; or directly:
   `(u * w)(single i 1) j = u (…) j` and row `j` of `u` is zero ⟹ evaluate); row of
   `c • 1` is `if j = i then c else 0` (`matrixCoeff` of `1` = `single_apply`).
2. `_of_rows`: both sides satisfy the same recursion in `m` with the same base.
   Base `m = 0`: `v₀ = 1` and `coeff 0` of `adjugate (1 − X•A)`: at `X = 0`,
   `adjugate 1 = 1` (`Matrix.adjugate_one`; coefficient-0 = evaluation at 0 —
   `Polynomial.coeff_zero_eq_eval_zero`, push through `adjugate` via `RingHom.mapMatrix`
   commuting with adjugate: `Matrix.adjugate_map`… simpler: use
   `Polynomial.evalRingHom 0` and `(1 − 0•A) = 1`). Step: from
   `Matrix.mul_adjugate` applied to `B := 1 − X•A`:
   `B * adj B = det B • 1`; read `Polynomial.coeff (m+1)` of both sides; LHS
   `= adjcoeff (m+1) − A·adjcoeff m` (the affine `B`), RHS `= cₘ₊₁·1` by
   `charCoeff_eq_det_coeff` (`Fredholm.lean:498`, hypothesis `hS` matches verbatim);
   this is the same relation `resolventCoeff_sub_mul` gives for the operator side,
   transported entrywise by `matrixCoeff_mul_of_rows` (rows of `resolventCoeff` stay
   supported… note: they do NOT stay supported off-diagonal — use `_of_notMem` to
   handle the identity-part bookkeeping when converting `u * w` entries: the sum over
   `k ∈ S` needs `w`'s rows off `S` — they contribute via `matrixCoeff u j k` with
   `k ∉ S`?? — `matrixCoeff_mul_of_rows` requires the INNER factor row-supported;
   here inner = `resolventCoeff u m` which is NOT row-supported (diagonal `cₘ` off
   `S`) — ATTENTION (recorded in decomposition B2 attack 3-adjacent): instead expand
   `u * w` with inner support-set `S ∪ {…}`?? Resolution: `u`'s COLUMNS off S:
   `matrixCoeff u j k` for `k ∉ S` need not vanish!  But `u * w (single i 1) j =
   u (w (single i 1)) j` — use instead the ROW-form: row `j ∈ S` of `u*w` is
   `Σ_k matrixCoeff u j k · matrixCoeff w k i` needing `w`-columns… Correct tool:
   since row `j` of `u` is a `c(I,R)`-functional with cofinite decay and
   `w (single i 1)` expands by `hasSum_single`, write
   `matrixCoeff (u*w) j i = Σ'_k matrixCoeff u j k * matrixCoeff w k i` (tsum form —
   prove as a general lemma via continuity of `evalCLM j ∘ u`; then split
   `k ∈ S` / `k ∉ S` where `_of_notMem` gives the off-part `= matrixCoeff u j i ·
   cₘ`-diagonal correction).  Follow the corrected computation:
   `(u·vₘ)[j,i] = Σ_{k∈S} u[j,k]vₘ[k,i] + u[j,i]·cₘ` and check the adjugate side
   satisfies the SAME corrected recursion (it does: `A` has columns only in… no —
   verify against the `S`-block identity: the matrix `A` is the `S×S` block; the
   claimed identity `adjcoeff (m+1) = A·adjcoeff m + cₘ₊₁·1` is pure `S×S`; the
   operator-side correction term `u[j,i]·cₘ` for `i,j ∈ S` equals
   `(A·(cₘ·1))[j,i]`'s missing piece… REDO carefully: with `w = vₘ`,
   `Σ_{k∈S} A[j,k]·vₘ[k,i] + Σ_{k∉S} u[j,k]·vₘ[k,i]` and `_of_notMem` gives
   `vₘ[k,i] = cₘ·δ_{k,i}` for `k ∉ S`; since `i ∈ S`, `δ_{k,i} = 0` — the correction
   VANISHES for `i ∈ S`. So the block recursion is exact after all; the tsum-form
   product lemma + `_of_notMem` (with `i ∈ S`) close it.)
   Conclude by induction (`Nat.rec` on the pair of sequences).
#### Mathlib/repo lemmas
`Matrix.mul_adjugate`, `Matrix.adjugate_one`?? (verify; else evaluation-at-0 route),
`charCoeff_eq_det_coeff`, `Polynomial.coeff_smul`?, `Polynomial.coeff_one`,
`hasSum_single`, `evalCLM` continuity. The tsum-form composition lemma may be worth
stating `private` (`matrixCoeff_mul_tsum`).
#### Sources
Serre p. 79 step a) ("les formules de Cramer … la matrice adjointe de 1 − tu") —
verbatim in decomposition B2. **Worker check (from attack log)**: verify
`adjugate_apply`'s index orientation against `mul_adjugate` on a 2×2 instance before
committing; flip with `adjugate_transpose` if needed.
#### Generality
Pure algebra over `R` (no `IsTate`, no compactness).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change; the ticket's
  corrected computation is exactly right and the off-support correction does vanish.
  **WORKER CHECK RESULT — orientation is CORRECT as stated, no `adjugate_transpose` needed.**
  Machine-verified on a 2×2 instance: `adjugate ![![a,b],![c,d]] = ![![d,-b],[-c,a]]`, i.e.
  `Matrix.adjugate_apply A i j = (A.updateRow j (Pi.single i 1)).det` replaces the row indexed
  by the SECOND index and puts the `1` at the FIRST index (adjugate = transpose of the cofactor
  matrix), consistent with `Matrix.mul_adjugate : A * adjugate A = A.det • 1`. Since the whole
  proof is read off `mul_adjugate` (never off `adjugate_apply`), the recursion produced is
  `V(m+1)[j,i] = Σ_k A[j,k]·V(m)[k,i] + c_{m+1}δ_{ji}`, which is the row-column product matching
  `matrixCoeff (u·w) j i`. (T010 *does* use `adjugate_apply` — mind the swap there.)
  **STATEMENT-ORDER FIX (no statement moved):** `_of_rows` is stated BEFORE `_of_notMem` but
  needs it; solved by a `private matrixCoeff_resolventCoeff_of_notMem'` placed before `_of_rows`,
  with the public `_of_notMem` reduced to a one-line delegation.
  New privates (file-scoped, reusable): `matrixCoeff_one (j i) : matrixCoeff 1 j i = if j = i
  then 1 else 0` (`cSpace.single_apply_self` / `single_apply_of_ne`, note the latter is
  `(h : j ≠ i) : single i r j = 0`); `hasSum_matrixCoeff_mul (u w) (j i) : HasSum (fun k =>
  matrixCoeff w k i * matrixCoeff u j k) (matrixCoeff (u*w) j i)` — the tsum-form product lemma
  the ticket anticipated, `= (cSpace.hasSum_single (w (single i 1))).mapL ((evalCLM j).comp u)`
  + `simp only [comp_apply, evalCLM_apply, map_smul, smul_eq_mul]` then plain `exact` (the last
  defeq `(u*w) x = u (w x)` is `rfl`); NEEDS NO `IsTate`, unlike `norm_apply_coord_le`.
  `_of_notMem'` needs no induction — `cases m` suffices (`resolventCoeff_succ` + the product row
  vanishing). `_of_rows` = `set B` + `hdet`/`hBentry`/`hBmul0`/`hBmul`/`hcramer`/`hprod` haves
  then `suffices h : ∀ n p q, … from h m j i` + `induction n`.
  **TRAPS (all cost a compile round):**
  * `Polynomial.mul_coeff_zero` fires on the FIRST product it meets, so `hBmul0` must
    `by_cases h : p = k` FIRST and go through `zero_sub`/`neg_mul`/`Polynomial.coeff_neg` in the
    negative branch instead of relying on `rw` order.
  * `rw [Subtype.coe_inj]` FAILS with "motive is not type correct" (the `Decidable` instance of
    `↑p = ↑q` depends on the rewritten proposition). Use `rcases eq_or_ne p q with rfl | hpq`
    and `if_neg fun hc => hpq (Subtype.ext hc)` for the coerced `if`, `if_neg hpq` for the
    subtype `if`. Note `rw [mul_one]`/`rw [mul_zero]` must be repeated (LHS and RHS are
    different instances of the pattern).
  * Name substitutions: **`Polynomial.finset_sum_coeff` → `Polynomial.finsetSum_coeff`**
    (deprecated 2026-04-08). `Finset.sum_ite_eq` is `@[simp]` in the `a = x` orientation and
    lands as `if a ∈ univ then …`; feed `Finset.mem_univ, if_true` to the same `simp only`.
  * `Finset.sum_coe_sort S f : ∑ i : S, f i = ∑ i ∈ S, f i` bridges `Matrix.mul_apply`'s
    `∑ k : ↥S` to `hasSum_sum_of_ne_finset_zero`'s `∑ k ∈ S`.
  * `charCoeff_eq_det_coeff` will not `rw` against a `set`-folded `B`; capture it once as
    `hdet : ∀ n, (Matrix.det B).coeff n = charCoeff u n` immediately after the `set`.

### [T009] Truncation continuity of the resolvent coefficients
- **Status**: done — **File**: Riesz.lean — **Depends on**: T007 — **Type**: lemma
#### Statement
`tendsto_resolventCoeff_truncation`.
#### Proof sketch
1. Fixed `m`: `resolventCoeff u' m − resolventCoeff u m` is a finite sum of
   `cₖ(u')u'^{m−k} − cₖ(u)u^{m−k}`; bound by `opNorm_sum_le` + telescoping each term:
   `‖cₖ(u')u'^j − cₖ(u)u^j‖ ≤ max (‖cₖ(u') − cₖ(u)‖·‖u'‖^j) (‖cₖ(u)‖·‖u'^j − u^j‖)`
   (insert-and-subtract + `norm_add_le`, `opNorm_mul_le`, `opNorm_pow_le`);
   `‖u'^j − u^j‖ ≤ (max ‖u‖ ‖u'‖)^{j−1}·‖u' − u‖·(j)`-free ultrametric telescoping
   (standard `pow` difference: `Σ u'^i (u'−u) u^{j−1−i}` and `opNorm_sum_le` gives
   max-bound — ultrametric, no factor `j`).
2. `cₖ`-difference: `norm_charCoeff_sub_le` (`Fredholm.lean:380`; hypotheses need
   both compactoid: truncated `u' = π_S ∘ u` is compactoid by
   `IsCompactoid.comp_left` (`Matrix.lean:533`) — NOTE orientation: `comp_left`
   composes on the left with `w`; check which of `comp_left/right` matches
   `(truncation S).comp u` and use it).
3. Assemble: everything is `≤ C(u,m) · ‖π_S∘u − u‖`; conclude by
   `tendsto_truncation_comp` (`Matrix.lean:445`) + `squeeze_zero`.
#### Mathlib/repo lemmas
`opNorm_sum_le`, `opNorm_mul_le`, `opNorm_pow_le`, `norm_charCoeff_sub_le`,
`IsCompactoid.comp_left`, `tendsto_truncation_comp`, `norm_truncation_apply_le`
(for `‖π_S∘u‖ ≤ ‖u‖ ⇒` uniform constants), `squeeze_zero`.
#### Sources
Serre p. 79 step c) (verbatim in decomposition B3).
#### Generality
`[IsTate R]`, compactoid `u`.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change. Simplification vs the
  sketch: NO explicit constant `C(u,m)` and NO telescoping identity are needed — each of the
  `m+1` summands is shown to tend to `0` separately and the whole thing closes with
  `tendsto_finsetSum` (**name substitution: `tendsto_finset_sum` → `tendsto_finsetSum`**,
  deprecated 2026-04-08). Structure: `hvD : ∀ S, ‖π_S∘u‖ ≤ ‖u‖` (`opNorm_le_of_forall` +
  `norm_truncation_apply_le` + `le_opNorm`, so `max ‖π_S∘u‖ ‖u‖ = ‖u‖` and every bound is
  `S`-uniform); `htr := tendsto_truncation_comp u hu`; `hpow`; `hc`; `hterm`; then
  `squeeze_zero` against `∑_{k ∈ range (m+1)} ‖…‖` with `rw [resolventCoeff, resolventCoeff,
  ← Finset.sum_sub_distrib]; exact opNorm_sum_le _ _`.
  Orientation confirmed: **`IsCompactoid.comp_left hu (truncation S) : IsCompactoid
  ((truncation S).comp u)`** — `comp_left` is the right one here (`hu.comp_left _`).
  New privates (file-scoped, reusable by T010–T012):
  * `opNorm_smul_le' (a : R) (w) : ‖a • w‖ ≤ ‖a‖ * ‖w‖` — **`OperatorNorm.lean` has NO `smul`
    version of `opNorm_mul_le`**; proved by `opNorm_le_of_forall` + `norm_smul_le` + `le_opNorm`
    (`(a • w) x = a • w x` is `rfl`). Needs `[IsTate R]` (via `le_opNorm`).
  * `tendsto_norm_pow_sub_pow (u) (v : α → End) (hD : ∀ x, ‖v x‖ ≤ D) (h : Tendsto (‖v · - u‖))
    (n) : Tendsto (‖v ·^n - u^n‖)` — induction on `n` through
    `v^{n+1} - u^{n+1} = vⁿ(v-u) + (vⁿ-uⁿ)u` (`rw [mul_sub, sub_mul, pow_succ, pow_succ]; abel`),
    no explicit constant.
  **TRAPS:**
  * **`(deterministic) timeout at whnf` (200000 hb)** from the calc step
    `add_le_add_right (mul_le_mul_of_nonneg_right hbnd (opNorm_nonneg _)) _`. FIX: hoist both
    summand bounds into `have h1 …` / `have h2 …` and close with `add_le_add h1 h2`. Do not
    leave `add_le_add_right`'s trailing `_` to be solved against the `squeeze_zero` metavariable.
  * **INDENTATION trap**: a multi-line `(by simpa using …)` supplied inline as a `refine`
    argument silently truncates the tactic term at the line break (continuation column < the
    `simpa` column) and reports "unexpected token '('". Always hoist the `squeeze_zero`
    third argument into a named `have hg : Tendsto … := by …` and pass `hg`.
  * `squeeze_zero` needs `(g := …)` given EXPLICITLY when the second argument is `fun S => ?_`.
  * `tendsto_const_nhds` cannot be `simpa`'d into a goal whose filter is a section variable
    (universe/filter metavariables). Use `simp only [pow_zero, sub_self, opNorm_zero]` (resp.
    `simp only [charCoeff_zero, sub_self, norm_zero]`) followed by `exact tendsto_const_nhds`.

### CLEANUP-3 — /cleanup on Riesz.lean (T007–T009)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T007, T008, T009 — **Type**: cleanup

### [T010] Lemme 3 bound and entireness of the resolvent (Serre Prop. 10)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T008, T009 — **Type**:
  lemma pair
#### Statement
`norm_resolventCoeff_le`, `tendsto_norm_resolventCoeff`.
#### Proof sketch
1. Row-supported case of the bound: entries via T008. On-block: `adjugate_apply` +
   `Matrix.det_apply` (Leibniz) on `(1 − X•A).updateRow i (Pi.single j 1)`; the
   `coeff m` of a permutation product `∏ (δ − X·a)`-entries with one `single`-row:
   nonzero contributions choose `m` distinct non-updated rows, each contributing
   `‖a_{p,σp}‖ ≤ rowNorm u p`; bound each by `∏_{p ∈ T} rowNorm u p`, `T.card = m`,
   then `≤ ⨆` (with `le_ciSup` — `BddAbove` from the `δ/D/b` threshold-split:
   finitely many rows above `δ`, rest `< δ ≤ 1`-controlled; mirror
   `Fredholm.lean:203–239`). Off-block: `_of_notMem` + `norm_tsum_le_iSup`
   (`Tate.lean:445`) + `norm_minor_le_prod` (restate the one-line consequence
   locally — it is `private` in Fredholm.lean; do NOT edit Fredholm.lean).
2. General case: T009 + limit of the bound (the RHS is `S`-independent; use
   `le_of_tendsto`).
3. `tendsto_norm_resolventCoeff`: from 1–2 with the repo's `δ/D/b` + `squeeze_zero'`
   pattern (`δ := min (1/(2M)) 1` etc., copied from `charPowerSeries_isEntire`'s
   inline argument).
#### Mathlib/repo lemmas
`Matrix.adjugate_apply`, `Matrix.det_apply` (or `Matrix.det_sum_of…` Leibniz
formulations), `Polynomial.coeff_prod`?, `norm_tsum_le_iSup`, `le_ciSup`,
`Real.iSup_le`, `le_of_tendsto`, `squeeze_zero'`, `Finset.prod_le_prod` (nonneg).
This is the technical core ticket; budget accordingly. If the Leibniz-coefficient
bookkeeping stalls, the fallback (recorded in decomposition B2c) is bounding
`‖adjcoeff m‖` through the RECURSION `adjcoeff (m+1) = A·adjcoeff m + cₘ₊₁1` by
strong induction with the sharpened inductive invariant "entry `(j,i)` is a
`±`-sum of products of distinct-row entries" stated as an explicit auxiliary
predicate — heavier but elementary.
#### Sources
Serre p. 79 (Lemme 3 + proof, verbatim in decomposition B2/B3); Prop. 10 p. 78.
#### Generality
`[IsTate R]`, compactoid.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change on either lemma.
  **ROUTE TAKEN: neither the Leibniz-coefficient route (1) nor the recursion fallback — a third,
  shorter route: ROW-MULTILINEARITY + DIAGONAL FACTORING.**  The fallback's recursion invariant is
  genuinely non-inductive (checked: `‖u‖·Pₘ ≰ Pₘ₊₁`, e.g. one row of norm 2 and the rest 0 gives
  `P₁ = 2`, `P₂ = 0`; the "avoid row `k`" sharpening is not inductive either, because
  `(vₘ)_{ki}` is only guaranteed to avoid `k`, not `j`), so the adjugate/Cramer route is forced —
  but the `det`-coefficient can be extracted WITHOUT any Leibniz/antidiagonal bookkeeping:
  * `MultilinearMap.map_add_univ` on the rows: `det (Y·C − X·A·C) = ∑_{s : Finset n}
    det (s.piecewise (−(X • A.map C)) (Y.map C))` (same trick as `det_one_sub_smul_eq_sum`).
  * `s.piecewise (−(X•A.map C)) (Y.map C) = diagonal (fun p => if p ∈ s then −X else 1)
    * (of (s.piecewise A Y)).map C`, so by `Matrix.det_mul` + `det_diagonal` + `prod_ite_mem` the
    summand is `(−X)^{s.card} · C (det (of (s.piecewise A Y)))`.
  * `coeff m` therefore kills every `s` with `s.card ≠ m` (`coeff_C_mul_X_pow`), and the
    surviving scalar determinants are bounded by the ultrametric Hadamard bound with row bounds
    `if p ∈ s then f p else 1`, i.e. by `∏_{p ∈ s} f p` with `|s| = m` — Serre's "m distinct
    rows" is exactly `s.card = m`.
  **Off-block case is unnecessary**: instead of splitting `j ∈ S` / `j ∉ S`, enlarge the support
  to `S' = insert j (insert i S)` (row-support is monotone in `S`), so T008's Cramer identity
  applies to EVERY pair `(j, i)`; `matrixCoeff_resolventCoeff_of_notMem` and `norm_minor_le_prod`
  are then not needed at all in T010.
  **`adjugate_apply` orientation** (the flagged trap) is handled by feeding
  `A := of fun p q => if p = ⟨i⟩ then 0 else matrixCoeff w p q` (the UPDATED row is the second
  index `i`) and `Y := of fun p q => if p = ⟨i⟩ then (if q = ⟨j⟩ then 1 else 0) else δ_{pq}`
  (the `1` sits at the FIRST index `j`).
  **FILE-ORDER FIX (no statement moved, T008 precedent):** `norm_resolventCoeff_le` is stated
  BEFORE `tendsto_resolventCoeff_truncation` (T009) but needs it.  Solved exactly as T008 did:
  a `private tendsto_resolventCoeff_truncation'` carrying T009's proof body is placed before
  `norm_resolventCoeff_le`, and the public T009 lemma keeps its statement/position with a
  one-line delegation.  The two private helpers T009 introduced (`opNorm_smul_le'`,
  `tendsto_norm_pow_sub_pow`) moved up with it — private helpers only, no public statement moved.
  New privates (file-scoped, reusable by T011–T012 and the T02x tier):
  * `norm_det_le_of_row_bounds'` — local restatement of Fredholm's private Hadamard bound
    (dropped its unused `hf0` argument).
  * `norm_neg_one_pow'` — local restatement of Fredholm's private `‖(−1)ⁿ‖ = 1`.
  * `norm_coeff_det_le (MC A Y f) (hMC : ∀ p q, MC p q = C (Y p q) − X * C (A p q)) (hA : ‖A p q‖
    ≤ f p) (hY : ‖Y p q‖ ≤ 1) (m) (hc : 0 ≤ c) (hcT : ∀ T, T.card = m → ∏_{p∈T} f p ≤ c) :
    ‖(det MC).coeff m‖ ≤ c` — **the reusable engine**; taking `hMC` entrywise (rather than
    `MC = Y.map C − X • A.map C`) keeps the call sites free of `Matrix.map`/`smul` unfolding.
    Phrasing the bound as "any `c` dominating the products" instead of an `iSup` avoids all
    `BddAbove` bookkeeping and the `Finset S' → Finset I` transfer inside the lemma.
  * `norm_matrixCoeff_le_rowNorm'`, `rowNorm_le_opNorm'` (both private in Fredholm/Matrix),
    `rowNorm_truncation_comp_le` (`rowNorm (π_S ∘ u) j ≤ rowNorm u j`),
    `norm_matrixCoeff_resolventCoeff_le_of_rows`, `norm_resolventCoeff_le_of_rows`,
    `prod_rowNorm_le` (the `δ/D/b` threshold split, stated for PRODUCTS of row norms rather than
    for minors — the `hminor` half of `charPowerSeries_isEntire`, reusable verbatim).
  **TRAPS (each cost a compile round):**
  * **`Finset.piecewise` lemmas do not `rw`/`simp` against `Matrix n n α`**: `Matrix` is
    semireducible, so `piecewise_eq_of_mem/_of_notMem` report "Did not find an occurrence"
    ("target expression is not type-correct under `implicit` transparency").  FIX: a local
    `have hpw : ∀ t U V r, t.piecewise U V r = if r ∈ t then U r else V r := fun _ _ _ _ => rfl`
    (one copy per coefficient ring) and `rw [hpw]`.
  * `s.piecewise A Y` elaborates at type `n → n → R`, NOT `Matrix n n R`; a type ascription does
    not fix it (`.map`/`*` then fail).  Wrap it as `Matrix.of (s.piecewise A Y)`.
  * `RingHom.map_det f M : f M.det = (f.mapMatrix M).det` — the RHS is `mapMatrix`, not
    `Matrix.map`, so `rw [← RingHom.map_det]` fails.  Capture it as a `have` and close with
    `exact (RingHom.map_det …).symm` (defeq, as `charCoeff_eq_det_coeff` already does).
  * `ext p q` on a `Matrix n n (Polynomial R)` goal keeps going into `Polynomial.ext` (goal gains
    a `.coeff n✝`).  Use `refine Matrix.ext fun p q => ?_`.
  * **`add_le_add_right h _` inside a `calc` again caused `(deterministic) timeout at whnf`**
    (the T009 trap, second sighting).  FIX: `add_le_add h le_rfl`.
  * `M →L[R] N` has NO `SeminormedAddCommGroup` instance in this development (only the scoped
    `Norm`), so **`norm_sub_le` does not typecheck** on operators.  Use the repo's
    `norm_add_le` on `a + -(a - b)` plus `opNorm_neg` (`congr 1; abel` for the rewriting step).
  * `Real.iSup_le`/`Real.iSup_nonneg` see through `rowNorm`'s `def` — no `rw [rowNorm]` needed.
  Both declarations `#print axioms`-clean; `lake build PhD.TateFredholm.Riesz` 0 errors.

### [T011] Divided evaluations exist and commute
- **Status**: done — **File**: Riesz.lean — **Depends on**: T001, T010 — **Type**:
  lemma pair
#### Statement
`exists_isOpLimit_resolventPartialSum`, `commute_of_isOpLimit_resolventPartialSum`.
#### Proof sketch
1. Existence: partial sums are ultrametric-Cauchy: for `n ≤ n'`,
   `‖Σ_{[n,n')} χₘ • aᵐ • vₘ₊ₛ‖ ≤ max over the range of `‖vₘ₊ₛ‖‖a‖ᵐ`
   (`opNorm_sum_le` + `‖χₘ‖ ≤ 1`: ℕ-cast norm ≤ 1 ultrametrically — verify name
   `IsUltrametricDist.norm_natCast_le_one`; fallback induction on `norm_add_le_max`);
   tail → 0 by T010 at `M := ‖a‖` (pad `M = 0` case). `exists_lim_of_cauchySeq`.
2. Commute: each partial sum is a polynomial in `u` (sum of `c • u^j`) ⟹ commutes
   (`Commute.sum_left/right`, `Commute.smul_*`, `(Commute.refl u).pow_right`);
   `u * N` and `N * u` are limits of the SAME sequence by T001 `.comp_left/.comp_right`
   + rewrite; `IsOpLimit.unique`.
#### Mathlib/repo lemmas
`exists_lim_of_cauchySeq`, `opNorm_sum_le`, ℕ-cast-norm bound, `Commute.*`,
T001 lemmas.
#### Sources
Serre p. 80 ("Les dérivées divisées Δˢ transforment une fonction entière en une
fonction entière"); decomposition B4/B5.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change on either lemma.
  **Route followed the sketch**, with two deviations recorded below.
  * **Ultrametric sum bound had to be BUILT.** `opNorm_sum_le` (`≤ ∑ ‖·‖`) is useless here: the
    summand norms are null but NOT summable, so the Cauchy estimate needs the max bound. New
    privates `opNorm_add_le_max'` (`‖w + w'‖ ≤ max ‖w‖ ‖w'‖`, from `IsUltrametricDist c(I,R)`
    at `ModelSpace.lean:89` through `opNorm_le_of_forall`) and `opNorm_sum_le_of_forall`
    (`(∀ i ∈ t, ‖f i‖ ≤ c) → ‖∑ i ∈ t, f i‖ ≤ c`, `Finset.induction_on` after `revert hf`).
  * **`M = 0` padding avoided entirely** by invoking T010 at `M := C = max ‖a‖ 1` instead of at
    `‖a‖`: then `‖a‖ᵐ ≤ Cᵐ ≤ C^(m+s)` (`pow_le_pow_left₀` then `pow_le_pow_right₀`) and the
    index shift `m ↦ m + s` is a plain `Tendsto.comp (tendsto_add_atTop_nat s)`. No division by
    `‖a‖ˢ`, no case split.
  * Cauchy packaging: `hterm.eventually_lt_const (half_pos hε)` + `Finset.eventually_atTop`, a
    `key : ∀ p q, M₀ ≤ p → p ≤ q → ‖P q − P p‖ ≤ ε/2` proved via
    `← Finset.sum_Ico_eq_sub _ hpq`, then `opNorm_sub_comm` for the `q ≤ p` half.
  * Commutation: no `Commute` API needed at all — `hpow : u * (b • uᵖ) = (b • uᵖ) * u` by
    `mul_smul_comm, smul_mul_assoc, ← pow_succ', ← pow_succ`, lifted through
    `Finset.mul_sum`/`Finset.sum_mul` to `resolventCoeff` and then to `resolventPartialSum`;
    finish `(hN.comp_left u).unique` after `rw [show (fun n => u * P n) = fun n => P n * u
    from funext hpart]`.
  New privates (file-scoped, reusable by T012 and the T02x tier): `opNorm_add_le_max'`,
  `opNorm_sum_le_of_forall`, `norm_natCast_le_one'`, `norm_natCast_mul_mul_pow_le`,
  `norm_natCast_smul_pow_smul_le`, `opNorm_smul_one_le`, `isOpLimit_shift`, `isOpLimit_congr`,
  `isOpLimit_zero_of_le`, `isOpLimit_smul_one`, `resolventPartialSum_succ`,
  `resolventPartialSum_one`, `mul_resolventCoeff`.
  **TRAPS:**
  * `IsUltrametricDist.norm_natCast_le_one` NOT used (per the batch correction):
    `norm_natCast_le_one'` goes `rw [← mul_one (k : R), ← nsmul_eq_mul]` then
    `IsUltrametricDist.norm_nsmul_le (1 : R) k` — note the argument order is `(x) (n)`.
  * **`IsOpLimit` does not unfold during elaboration of `Filter.Tendsto.comp`/`.congr`**: writing
    `Filter.Tendsto.comp h …` with `h : IsOpLimit T L` gives "expected `Tendsto norm …`" (the
    elaborator picks `‖·‖` as the outer function). FIX: re-ascribe first
    (`have h' : Tendsto (fun n => ‖T n - L‖) atTop (𝓝 0) := h`), and for the goal side add an
    explicit `show Tendsto …`; for `.comp` use `have h'' := h'.comp …; exact h''` so the
    composite is elaborated WITHOUT the expected type.
  * `ContinuousLinearMap.add_apply` is deprecated — use `show ‖w x + w' x‖ ≤ …` instead.

### [T012] The evaluated identities (Serre's Δˢ equations)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T003, T004, T007, T011 —
  **Type**: lemma pair
#### Statement
`one_sub_smul_mul_resolventEval_zero`, `one_sub_smul_mul_resolventEval`.
#### Proof sketch
1. Coefficient identity (s ≥ 1), proved first as a `private` lemma:
   `χ(m+s,s)vₘ₊ₛ − χ(m−1+s,s)·(u·vₘ₊ₛ₋₁)`-form — concretely, using
   `resolventCoeff_succ`:
   `χ • vₘ₊ₛ = χ • (cₘ₊ₛ • 1) + χ • (u * vₘ₊ₛ₋₁)` and Pascal
   `χ(m+s,s) = χ(m−1+s,s) + χ(m+s−1,s−1)` (`Nat.choose_succ_succ` after index
   normalisation).
2. `(1 − a•u) * (partial n)`: expand by `mul_sub`/`Finset.mul_sum`, apply 1 to each
   term, telescope the `u·vₘ₊ₛ₋₁`-parts against the `s−1`-partial sum; boundary
   term `‖aⁿ·(stuff)‖ → 0` by T010.
3. Pass to the limit: LHS via T001 `.comp_left` on `hN`; RHS: `u * N'` via
   `.comp_left` on `hN'`; the scalar part: partial sums of
   `χ·cₘ₊ₛ·aᵐ` converge to `evalT a (hasseDeriv s H)` — `coeff_hasseDeriv` (T003)
   aligns the summand, summability from `charPowerSeries_isEntire` at radius
   `> ‖a‖`-adjacent (T004's bridge), `HasSum`→`IsOpLimit` of `• 1` scalars
   (`‖(c − c') • 1‖ ≤ ‖c − c'‖`, `opNorm_one_le`-scaled — small glue).
   Conclude equality by `IsOpLimit.unique`.
4. `s = 0` version: same with `resolventCoeff_sub_mul` directly (no `N'`, no Pascal).
#### Mathlib/repo lemmas
`Nat.choose_succ_succ` (+ index gymnastics `Nat.succ_pred_eq_of_pos`),
`Finset.mul_sum`, `mul_sub`, `charPowerSeries_isEntire`, `opNorm_one_le`, T001/T003/
T004/T007/T010/T011 outputs.
#### Sources
Serre pp. 80–81 (verbatim in decomposition B6); planning-time hand-derivation of the
Pascal step recorded there — worker re-derives before coding.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change on either lemma.
  **PASCAL STEP AS ACTUALLY USED** (re-derived from scratch and machine-checked on random
  rationals for `t ≤ 4`, `n ≤ 5`, before any Lean was written):
  `C(n+t+2, t+1) = C(n+t+1, t+1) + C(n+t+1, t)`, i.e. in the `s = t+1` convention
  `C(m+s, s) = C(m−1+s, s) + C(m−1+s, s−1)`. Lean form:
  `rw [show n+t+2 = n+t+1+1 from rfl, Nat.choose_succ_succ' (n+t+1) t]; push_cast; ring`
  (`Nat.choose_succ_succ' (n k) : (n+1).choose (k+1) = n.choose k + n.choose (k+1)` — the
  rw-matching orientation, as flagged).
  **ROUTE: two `private` FINITE identities proved by induction on `n`, then one limit passage
  each.** No termwise-then-telescope bookkeeping, no `Finset.sum_range_succ'` re-indexing —
  induction absorbs the re-indexing for free, and `module` closes both induction steps.
  * `one_sub_smul_mul_resolventPartialSum_zero` (all `n`, no `s ≥ 1`):
    `(1 − a•u) · P₀(n) = (∑_{j<n+1} c_j aʲ)•1 − aⁿ•vₙ`.
  * `one_sub_smul_mul_resolventPartialSum_succ` (indices normalised to `+ t + k`; note it is
    stated at `n+1`, NOT at `n` — at `n = 0` the truncated `n−1` boundary coefficient would
    break it):
    `(1 − a•u) · P_{t+1}(n+1) = u · P_t(n+1) + (∑_{m<n+1} C(m+t+1,t+1)·c_{m+t+1}·aᵐ)•1
      + (C(n+t+1,t+1)·c_{n+t+2}·aⁿ⁺¹)•1 − C(n+t+1,t+1) • aⁿ⁺¹ • v_{n+t+2}`.
  * Both proofs: `simp only [sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, <recursion>]`
    then `module` (the `Mathlib.Tactic.Module` tactic — it normalises `r • s • x` and calls
    `ring` on the coefficients, so `a·aⁿ⁺¹ = aⁿ⁺²` needs no hand step).
  * Limit passage: `IsOpLimit.add` chained three times against `isOpLimit_shift (hN.comp_left …)
    1`, `isOpLimit_smul_one hSc`, and two `isOpLimit_zero_of_le` boundary terms, then
    `isOpLimit_congr` with the finite identity + `abel`, then `IsOpLimit.unique`.
    Scalar side `hSc`: `PowerSeries.coeff_hasseDeriv` + `charPowerSeries_coeff` align the
    summand with `Sc`, summability from `isRestricted_hasseDeriv` (private, same file) at
    `C = max ‖a‖ 1` via `summable_coeff_mul_pow`, then `HasSum.tendsto_sum_nat` composed with
    `tendsto_add_atTop_nat 1`.
  New privates: `resolventPartialSum_zero_succ`, `one_sub_smul_mul_resolventPartialSum_zero`,
  `one_sub_smul_mul_resolventPartialSum_succ` (plus everything listed under T011).
  **TRAPS (each cost a compile round):**
  * **Nat index normal forms are the whole difficulty.** `m + (t+1)` is *defeq* to `m + t + 1`
    but never *syntactically* equal, so `rw`/`simp`/`module` see different atoms. FIXES used:
    (a) state every private in the `+ t + k` normal form and let defeq do the transport
    (`resolventPartialSum_one`, `hP1`, `hP2` all typecheck by `rfl` modulo an explicit
    `show n + 1 + (t+1) = n + t + 2 from by omega` rewrite);
    (b) instantiate `mul_resolventCoeff` into local `have hv1/hv2` with the DESIRED index shape
    rather than putting the generic lemma in the simp set — this is what removes the `n+t+1+1`
    vs `n+t+2` mismatch;
    (c) `rw` closes with `rfl` at *reducible* transparency only, so
    `rw [coeff_hasseDeriv, charPowerSeries_coeff]` leaves `m+t+1` vs `m+(t+1)` open — append a
    bare `rfl`.
  * **DO NOT put `∀ k, k+1+1 = k+2` / `∀ k, k+2+1 = k+3` in a `simp only` set**: simp reports
    "Possibly looping simp theorem" and then dies with `maximum recursion depth`. Use (b) above.
  * `rw [Finset.sum_range_succ]` rewrites the FIRST match, which is the `range (n+1)` coming
    from the induction hypothesis, not the `range (n+2)` of the goal. Use
    `simp only [Finset.sum_range_succ]` (it expands both consistently and cannot loop, since
    `range n` does not match `range (?k+1)`).
  * In the `n = 0` base of the zero-identity, ONE `rw [one_smul]` discharges both occurrences
    (they are literally the same term `(1 : R) • (1 : c(I,R) →L[R] c(I,R))`); a second
    `one_smul` then fails with "did not find an occurrence".
  * `Filter.Tendsto.comp` under an expected type containing `evalT`/`IsOpLimit` mis-elaborates
    (unifies against `Multiset.sum` / `norm`). Always `have h2 := h1.comp …; exact h2`.

### CLEANUP-4 — /cleanup on Riesz.lean (T010–T012)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T010, T011, T012 — **Type**: cleanup

### [T013] Determinant value and scaling
- **Status**: done — **File**: Riesz.lean — **Depends on**: T004 — **Parallel**: yes —
  **Type**: def API
#### Statement
`charCoeff_smul`, `fredholmDet_smul`.
#### Proof sketch
1. `charCoeff_smul`: `minor (a•u) S = a^S.card * minor u S` via `matrixCoeff_smul`
   (T002) + `Matrix.det_smul` (matrix is `a • (block)` — `Matrix.of` ext); then
   `charCoeff`: `tsum` commutes with `a^n * ·` (`tsum_mul_left`), signs collected.
2. `fredholmDet_smul`: unfold both `evalT`s; `charCoeff_smul` + `mul_pow`,
   `one_pow`; summability side conditions from `charPowerSeries_isEntire` (`C := 1`
   and `C := max ‖a‖ 1`) through T004's bridge.
#### Mathlib lemmas
`Matrix.det_smul` (verified `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:272`),
`tsum_mul_left`, `mul_pow`.
#### Sources
Serre p. 75 ("le cas général en résulte par homothétie"); decomposition C1.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change. Both lemmas came out
  exactly as sketched, no new privates.
  * `charCoeff_smul`: the matrix identity
    `(Matrix.of fun j i : ↥S => matrixCoeff (a•u) ↑j ↑i) = a • Matrix.of fun j i : ↥S => …`
    is `Matrix.ext fun _ _ => rfl` (`matrixCoeff_smul` and `Matrix.smul_apply` are both `rfl`),
    then `Matrix.det_smul` + `Fintype.card_coe` + `S.2` (the `Fredholm.lean:401` pattern), then
    `tsum_congr` + `(summable_minor u hu n).tsum_mul_left` + `ring`. **`hu` IS used** — `R` is
    not a division ring, so the unconditional `tsum_mul_left` does not apply and
    `Summable.tsum_mul_left` is needed.
  * `fredholmDet_smul`: NO summability side conditions at all — the identity is *termwise*
    (`coeff n (charPowerSeries (a•u)) * 1ⁿ = aⁿ·cₙ(u) = cₙ(u) * aⁿ`), so
    `refine tsum_congr fun n => ?_` then `charPowerSeries_coeff`, `charCoeff_smul`, `one_pow`,
    `mul_one`, `mul_comm`. The T004 bridge / `charPowerSeries_isEntire` route in the sketch is
    unnecessary.
  * Trap: `minor` is a `def`, so unfold it with `rw [show minor v T = Matrix.det (…) from rfl]`
    (the `Fredholm.lean:539` idiom); `show Matrix.det _ = _` is fragile (instance holes).

### [T014] Determinant value of a row-supported operator
- **Status**: done — **File**: Riesz.lean — **Depends on**: T013 — **Type**: lemma
#### Statement
`fredholmDet_eq_det_of_rows`.
#### Proof sketch
1. `charCoeff_eq_det_coeff` gives `cₙ = coeff n (det (1 − X • blockC))`.
2. The det-polynomial `p` has `natDegree ≤ S.card` (each Leibniz term is a product of
   `S.card` affine entries — `Polynomial.natDegree_det_le`-search; if absent, prove
   coefficient-vanishing for `n > S.card` from `charCoeff` directly: minors over
   `n`-subsets need `n` distinct rows in `S`).
3. `evalT 1 (mk (p.coeff ·))`: `tsum_eq_sum` over `range (S.card + 1)`
   (`1 ^ n = 1`), which is `p.eval 1` (`Polynomial.eval_eq_sum_range`); and
   `p.eval 1 = det (1 − blockR)` (`Polynomial.eval` is a ring hom through the
   matrix: `Matrix.det_map`-style with `Polynomial.evalRingHom 1`, or
   `RingHom.map_det`).
#### Mathlib lemmas
`RingHom.map_det` (verify name; `Matrix.det_map`?), `Polynomial.eval_eq_sum_range`,
`tsum_eq_sum`, `Polynomial.coeff_natDegree`-adjacent.
#### Sources
Serre p. 76, Prop. 7 d) (verbatim in decomposition C2).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, no new privates.
  **ROUTE: the sketch's fallback (coefficient-vanishing from `charCoeff` directly), not a
  `Polynomial.natDegree_det_le` search** — the fallback is 8 lines and gives the degree bound
  for free:
  1. `hvanish : ∀ n, S.card < n → charCoeff u n = 0` — an `n`-set `T` with `n > S.card` cannot
     be `⊆ S` (`Finset.card_le_card` + `omega`), so it has a row `j ∉ S` which is zero by `hS`:
     `Matrix.det_eq_zero_of_row_eq_zero ⟨j, hjT⟩`; then `tsum_congr` + `tsum_zero` + `mul_zero`.
  2. `charCoeff_eq_det_coeff` transports `hvanish` to `p.coeff`, and
     `Polynomial.natDegree_le_iff_coeff_eq_zero` + `Nat.lt_succ_of_le` gives
     `p.natDegree < S.card + 1`.
  3. `fredholmDet u = ∑_{n < S.card+1} p.coeff n * 1ⁿ` by `tsum_eq_sum`, and that sum is
     `p.eval 1` by `Polynomial.eval_eq_sum_range' hdeg 1` (used with `←`).
  4. `p.eval 1 = det(1 − A_S)` by `RingHom.map_det (Polynomial.evalRingHom 1)`.
  * Traps: `RingHom.map_det` yields `f.mapMatrix M`, so the entrywise step is
    `rw [RingHom.mapMatrix_apply, Matrix.map_apply]` then `by_cases hxy : x = y` +
    `simp [Matrix.one_apply_ne hxy]` (bare `simp` in the `x = y` branch). `rw` needs the
    coercion bridged by hand: `have h1 : Polynomial.eval (1:R) p = (Polynomial.evalRingHom 1) p
    := rfl` (`rfl` does work at default transparency) — `rw [← Polynomial.coe_evalRingHom]` is
    not needed. Bind the det-polynomial with
    `obtain ⟨p, hp⟩ : ∃ p, p = … := ⟨_, rfl⟩` rather than `set` (keeps `rw [hp]` available and
    makes the `charCoeff_eq_det_coeff` shape match syntactically).

### [T015] Serre's Proposition 8: uniform coefficient convergence
- **Status**: done — **File**: Riesz.lean — **Depends on**: none of B/C (only
  Fredholm.lean's public API) — **Parallel**: yes (early start possible) — **Type**:
  lemma
#### Statement
`eventually_norm_charCoeff_sub_le`.
#### Proof sketch (Serre p. 77, adapted to the repo's threshold pattern)
1. Fix `ε`. `δ/D/b` data for `u` at radius `M`: `δ := …`, finitely many `M`-bad rows
   (`hu` cofinite), `D := max ‖u‖ 1 + 1` (a norm bound eventually valid for `w n`
   too, since `‖w n‖ ≤ ‖w n − u‖ + ‖u‖`).
2. For `n` with `‖w n − u‖ ≤ η`: each minor difference over an `m`-set `S` — Serre's
   "somme de produits de différences": telescope row-by-row (the repo's private
   `norm_det_sub_det_le` technique — REPROVE locally as a `private` lemma with the
   row-product refinement: `‖det A − det B‖ ≤ max_{i∈S} (‖rowdiff i‖ · ∏_{j ≠ i}
   max (rowNorm-bound j))`); rows differ by ≤ η, other rows bounded by
   `max (r_j(u), η)`-type; with the threshold split this is
   `≤ η · D^b · (max δ η)^{m−1−b}`-shaped, so `· Mᵐ ≤ ε` for ALL `m`
   simultaneously once `η` small (two regimes: `m ≤ m₀` finitely many — continuity
   in `η`; `m > m₀` — the `δᵐ`-decay kills `Mᵐ` regardless; Serre's finitely-many-
   `rᵢ > 1` bookkeeping).
3. `charCoeff` difference: `norm_tsum_le_iSup` of minor differences (both tsums —
   subtract termwise; `tsum_sub` with the two summabilities).
#### Mathlib/repo lemmas
`norm_tsum_le_iSup`, `summable_minor`, `tendsto_minor_cofinite`-pattern, local
row-telescoping lemma, `squeeze` bookkeeping. Heavy bookkeeping, elementary content.
#### Sources
Serre p. 77, Prop. 8 (verbatim in decomposition C0, including the planning-time
attack that showed `norm_charCoeff_sub_le` alone is insufficient at `M ≥ 1`).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change. **T010's engine was
  REUSED for the product side and a NEW telescoping engine was written for the difference
  side** — `norm_det_le_of_row_bounds'` (T010) is the workhorse inside the new lemma, but
  `prod_rowNorm_le` could NOT be reused verbatim (it is hard-wired to `rowNorm u` and the
  estimate needs `g j := max (rowNorm u j) η`, on the *subtype* `↥T`), so it was generalised.
  **THREE NEW PRIVATES** (all placed just above `eventually_norm_charCoeff_sub_le`):
  * `prod_le_of_threshold` — abstract `δ/D/b` split: `{g : n → ℝ}` nonneg, `≤ D` everywhere,
    `≤ δ` off a decidable predicate `P` with `(s.filter P).card ≤ b`, and `k ≤ s.card`, gives
    `∏_{j ∈ s} g j ≤ Dᵇ δ^{k−b}`. Same proof as `prod_rowNorm_le` (filter split +
    `pow_le_pow_right₀` / `pow_le_pow_of_le_one`); the predicate form is what lets it run on
    `(Finset.univ.erase p : Finset ↥T)` — **this is what avoids the ugly
    `∏ q ∈ univ.erase p, g ↑q = ∏ j ∈ T.erase ↑p, g j` subtype/erase product conversion.**
  * `norm_det_sub_det_le'` — the refined row-telescoping ("somme de produits de différences"):
    `hA/hB : ∀ p q, ‖· p q‖ ≤ f p`, `hAB : ∀ p q, ‖A p q − B p q‖ ≤ ε`,
    `hprod : ∀ p, ∏_{q ≠ p} f q ≤ c` ⟹ `‖det A − det B‖ ≤ ε·c`. Structure copied from
    `Fredholm.lean:273` (hybrid matrices `H t`, `Finset.sum_range_sub`,
    `Matrix.det_updateRow_add`) with the *global* bound `M` replaced by the *row* bound `f p`
    and the final product step becoming `ε * ∏_{q ≠ p} f q`. The `Fintype.card n = 0` case is
    split off at the top (`Matrix.det_isEmpty` twice) so no `1 ≤ card` hypothesis is needed.
  * `norm_minor_sub_minor_le` — glue: `‖minor v T − minor u T‖ ≤ η·(D^{|B|} δ^{m−1−|B|})`
    for `T.card = m`, by the two above with `f := fun q : ↥T => g ↑q`,
    `s := Finset.univ.erase p`, `b := B.card`, `k := m − 1`
    (`Finset.card_le_card_of_injOn Subtype.val` for the filter-card bound;
    `Finset.card_erase_of_mem` + `Finset.card_univ` + `Fintype.card_coe` + `omega` for `hk`).
  **MAIN PROOF SHAPE** (all thresholds chosen up front, `m` never case-split at top level):
  `C := max M 1`, `δ := min (1/(2C)) 1` (so `δC ≤ 1/2`), `D := max ‖u‖ 1`,
  `b := |{j | δ ≤ rowNorm u j}|` (finite by `hu`), `K := C^{b+1}/δᵇ`,
  `η := min (min δ 1) (ε/(Dᵇ·K))`. For `‖wₙ − u‖ ≤ η` put `g j := max (rowNorm u j) η`; then
  `rowNorm (wₙ) j ≤ max (rowNorm (wₙ−u) j) (rowNorm u j) ≤ g j` (ultrametric `rowNorm_add_le`
  on `(wₙ−u)+u`, `rwa [sub_add_cancel]`), `g ≤ D` (`η ≤ 1 ≤ D`), and `g ≤ δ` off the bad set
  (`η ≤ δ`). `charCoeff` difference = `(−1)ᵐ · ∑'` of minor differences
  (`HasSum.sub` + `norm_tsum_le_iSup` + `Real.iSup_le`; the cofinite tendsto comes from
  `Summable.tendsto_cofinite_zero`, since `tendsto_minor_cofinite` is private in Fredholm.lean).
  The `m`-uniform arithmetic lemma is `hKbound : ∀ m, δ^{m−1−b}·Cᵐ ≤ K`, proved after
  `rw [le_div_iff₀]` by `by_cases m − 1 ≤ b`: below threshold the `δ`-power is `δ⁰ = 1` and
  `Cᵐ ≤ C^{b+1}`; above it `δ^{m−1−b}·Cᵐ·δᵇ = (δC)^{m−1}·C ≤ 2^{−(m−1)}·C ≤ C^{b+1}`.
  `m = 0` needs no special case (`δ⁰C⁰ = 1 ≤ K`).
  **TRAPS:**
  * `Summable.tendsto_cofinite_zero` is the `to_additive` image of
    `Multipliable.tendsto_cofinite_one` (`InfiniteSum/Group.lean:365`) — it does NOT appear
    under its own name in a `grep` for `theorem …tendsto_cofinite_zero`.
  * Avoid `pow_sub₀`/division juggling in the threshold arithmetic: `rw [le_div_iff₀ hδᵇ]`
    FIRST, then the `δᵇ` factor recombines by `← pow_add` + `omega` in the hard branch and is
    just bounded by `1` in the easy branch.
  * `le_or_lt`/`rcases` on `m − 1 ≤ b` is fine, but `by_cases` is better: `omega` then has the
    negated ℕ-subtraction hypothesis in context for all four index identities
    (`m−1−b = 0`, `m−1−b+b = m−1`, `m−1+1 = m`, `m ≤ b+1`).
  * `set X := e` *without* `with h` where `h` is unused — otherwise the unusedVariables linter
    fires on every threshold constant.
  * `Finset.card_filter_add_card_filter_not` carries a second instance `[∀ x, Decidable (¬p x)]`;
    do NOT put `classical` in `prod_le_of_threshold` or the two `filter (¬ P ·)` occurrences can
    pick different instances and `omega`/`rw` stop matching.

### CLEANUP-5 — /cleanup on Riesz.lean (T013–T015)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T013, T014, T015 — **Type**: cleanup

### [T016] Multiplicativity of the determinant value (Serre Cor. 1)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T002, T013, T014, T015 —
  **Type**: lemma
#### Statement
`fredholmDet_mul`.
#### Proof sketch
1. Truncation pairs: `uₙ := π_{Sₙ}∘u`, `vₙ := π_{Sₙ}∘v` along a monotone ℕ-indexed
   exhaustion `Sₙ` chosen cofinally for BOTH rowNorm-decays (e.g. `Sₙ :=` the union
   of the `1/n`-bad finsets of `u` and `v` — finite by compactoidness); then
   `‖uₙ − u‖ = sup_{j∉Sₙ} rowNorm u j → 0` (via `norm_eq_iSup_matrixCoeff`;
   or directly `tendsto_truncation_comp` composed with the cofinal map — the ℕ-vs-
   Finset filter bridge recorded in decomposition C3 attack (2); either route).
2. `wₙ := uₙ + vₙ − uₙ*vₙ` is row-supported in `Sₙ` (rows off `Sₙ`: each summand's
   row vanishes — `π` kills them; for the product, `e_j ∘ π_{Sₙ} = 0`); and
   `wₙ → u + v − u*v` in norm (T002 arithmetic + `opNorm_mul_le` insert-and-subtract
   + `norm_truncation_apply_le`-derived `‖π∘x‖ ≤ ‖x‖`).
3. Finite case: `fredholmDet_eq_det_of_rows` on `uₙ`, `vₙ`, `wₙ` (same `Sₙ`);
   matrix identity `1 − W = (1 − Uₙ)(1 − Vₙ)` where `W`-block of `wₙ`:
   `matrixCoeff_mul_of_rows` (T002) converts the operator product to the matrix
   product on the block; `Matrix.det_mul`.
4. Limit: T015 on the three sequences (`M := 1`) gives
   `fredholmDet wₙ → fredholmDet (u+v−uv)` etc. (value difference ≤ sup-coefficient
   difference: `‖evalT 1 f − evalT 1 g‖ ≤ ⨆ m, ‖coeff m (f−g)‖` via
   `norm_tsum_le_iSup` — small glue lemma); products of limits (`Tendsto.mul` in
   `R`); uniqueness of limits in `R` (T2).
#### Mathlib/repo lemmas
`Matrix.det_mul`, `tendsto_truncation_comp`, `norm_eq_iSup_matrixCoeff`,
`norm_tsum_le_iSup`, `Tendsto.mul`, `tendsto_nhds_unique`, T002/T013/T014/T015.
#### Sources
Serre p. 76, Cor. 1 (verbatim in decomposition C3, with the sign-orientation check
`1−(u+v−uv) = (1−u)(1−v)` recorded).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change. The sign
  orientation checked out verbatim: `1 − (x + y − x·y) = (1 − x)(1 − y)` in the
  *noncommutative* matrix ring, discharged by `noncomm_ring` with `x·y` in that order.
  **FILTER-BRIDGE ROUTE USED: route (1), the "bad finsets" construction** — NOT the
  `tendsto_truncation_comp`-composed-with-a-cofinal-map route (that one needs a monotone
  cofinal `ℕ → Finset I`, i.e. `I` countable; unavailable here). Instead
  `Sₙ := {j | 1/(n+1) ≤ rowNorm u j}ᶠⁱⁿ ∪ {j | 1/(n+1) ≤ rowNorm v j}ᶠⁱⁿ` (finite by
  compactoidness), and `‖π_{Sₙ}∘w − w‖ ≤ 1/(n+1)` for `w ∈ {u, v}` by the restated tail bound;
  `squeeze_zero` against `tendsto_one_div_add_atTop_nhds_zero_nat`. Monotonicity of `Sₙ` is
  never needed — only the two norm limits are.
  **SEVEN NEW PRIVATES** (all in `section DetValue`, immediately above `fredholmDet_mul`):
  * `matrixCoeff_truncation_mul` — `matrixCoeff (π_S * u) j i = if j ∈ S then … else 0`,
    literally `rfl` (`*` on `→L` is `comp`, `truncation_apply` is `rfl`).
  * `norm_truncation_mul_sub_le` — restatement of `Matrix.lean`'s private
    `norm_truncation_comp_sub_le` in `*`-form (via `norm_eq_iSup_matrixCoeff` +
    `norm_matrixCoeff_le_rowNorm'`).
  * `exists_truncation_seq` — the filter bridge itself (statement: `∃ S : ℕ → Finset I`, both
    truncation-norm sequences `→ 0`).
  * `summable_charCoeff_one` — entireness at radius `1`, `‖(1:R)‖ ≤ 1` via `norm_one.le`.
  * `norm_fredholmDet_sub_le` — the "value difference ≤ sup coefficient difference" glue:
    `HasSum.sub` + `norm_tsum_le_iSup` + `Real.iSup_le`.
  * `tendsto_fredholmDet` — T015 at `M = 1` packaged as
    `‖wₙ − u‖ → 0 ⟹ fredholmDet wₙ → fredholmDet u` (`Metric.tendsto_nhds` + `filter_upwards`).
  * `fredholmDet_mul_of_rows` — **the finite case, factored out as its own lemma**: for `x`,`y`
    supported on the *same* `S`, `fredholmDet (x+y−xy) = fredholmDet x · fredholmDet y`, by
    T014 three times + `matrixCoeff_mul_of_rows` + `Matrix.det_mul`. Factoring this out (rather
    than inlining at each `n`) is what keeps the main proof readable.
  * plus `fredholmDet_zero` (private, needed by T017): minors of size `≥ 1` of `0` vanish
    (`Matrix.det_zero` with `Finset.Nonempty.to_subtype`), so `evalT 1 (charPowerSeries 0) = 1`
    by `tsum_eq_single 0`.
  **MAIN PROOF SHAPE:** `Uₙ := π_{Sₙ}·u`, `Vₙ := π_{Sₙ}·v`, `Wₙ := Uₙ + Vₙ − Uₙ·Vₙ`;
  `hfin n` from `fredholmDet_mul_of_rows`; compactoidness of `Uₙ/Vₙ` from
  `IsCompactoid.comp_left`, of `Wₙ` from `.add`/`.sub`/`.comp_right`; `Wₙ → u+v−uv` by
  `Wₙ − (u+v−uv) = ((Uₙ−u)+(Vₙ−v)) − ((Uₙ−u)·Vₙ + u·(Vₙ−v))` (`noncomm_ring`) with
  `‖π_S‖ ≤ 1` giving `‖Vₙ‖ ≤ ‖v‖`; then `tendsto_nhds_unique` against `Tendsto.mul`.
  **TRAPS:**
  * `isUnit_of_mul_eq_one` NO LONGER EXISTS — it is now `IsUnit.of_mul_eq_one (b) (h : a*b = 1)`
    with an `[IsDedekindFiniteMonoid M]` hypothesis (auto for `CommMonoid`).
  * `squeeze_zero` needed `(g := fun n : ℕ => 1 / (n + 1 : ℝ))` explicitly (the trap list's
    warning fired here).
  * `Finset.sum_coe_sort S f : ∑ k : ↥S, f ↑k = ∑ k ∈ S, f k` is the exact bridge between
    `Matrix.mul_apply` (over `Fintype ↥S`) and `matrixCoeff_mul_of_rows` (over `Finset I`);
    `rw [← Finset.sum_coe_sort …]` then `rfl`.
  * Operators still have no `SeminormedAddCommGroup`: `‖A − B‖ ≤ ‖A‖ + ‖B‖` had to be a local
    `have` proved by `rw [sub_eq_add_neg]` + `norm_add_le` + `opNorm_neg`.

### [T017] Serre's Proposition 11 (both directions + iff)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T011, T012 (⟸); T002,
  T016 (⟹) — **Type**: theorem pair + assembly
#### Statement
`isUnit_one_sub_smul_of_isUnit_evalT`, `isUnit_evalT_of_isUnit_one_sub_smul`,
`isUnit_one_sub_smul_iff_isUnit_evalT`.
#### Proof sketch
1. (⟸) Obtain `N₀` (T011); `one_sub_smul_mul_resolventEval_zero` (T012) gives
   `(1−a•u) * N₀ = H(a) • 1`; with `hd : IsUnit (H(a))`, the operator
   `hd.unit⁻¹ • N₀` is a right inverse; left by `commute_…` (T011);
   `isUnit_of_mul_eq_one` twice / `isUnit_iff_exists`.
2. (⟹) `h.unit⁻¹ =: w`; `v := 1 − w`; ring: `v = −(a•u) + (a•u)*v` from
   `(1−a•u)*w = 1`; `IsCompactoid v` by T002 (`.smul`, `.neg`, `.add`) +
   `IsCompactoid.comp_left` on `(a•u)*v`… (orientation: `(a•u)*v = (a•u).comp v`,
   compactoid by `comp_right` of `hu.smul` — check orientation at compile);
   `fredholmDet_mul` (T016) with `x := a•u`, `y := v`: `x + y − x*y = 0` (ring, from
   the inverse identity); `fredholmDet 0 = 1` (small step: `charCoeff 0 n` for
   `n ≥ 1` vanishes — minors of the zero operator; `evalT` of `1`); so
   `fredholmDet (a•u) * fredholmDet v = 1`; `fredholmDet (a•u) = evalT a H` (T013);
   `isUnit_of_mul_eq_one`.
3. Iff: `⟨2, 1⟩`.
#### Mathlib lemmas
`isUnit_of_mul_eq_one`, `IsUnit.unit⁻¹`-API, ring rearrangements; T-outputs listed.
#### Sources
Serre p. 80, Prop. 11 (verbatim both directions in decomposition D1/D2, including
the recorded dead-end attack that justifies routing through T016).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new helper
  needed beyond T016's `fredholmDet_zero`. Both directions went through exactly as sketched.
  * (⟸) `exists_isOpLimit_resolventPartialSum … a 0` → `N`; `(1−a•u)·N = H(a)•1` (T012);
    two-sidedness from `commute_of_isOpLimit_resolventPartialSum` via
    `(1−a•u)·N = N·(1−a•u)` (`sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, hcomm`); inverse `(↑hd.unit⁻¹ : R) • N`; concluded with
    `isUnit_iff_exists.2 ⟨…, hright, hleft⟩` (the operator ring is NOT commutative, so
    `IsUnit.of_mul_eq_one` is unavailable there).
  * (⟹) `obtain ⟨w, hw, -⟩ := isUnit_iff_exists.1 h` — only the RIGHT inverse equation
    `(1−a•u)·w = 1` is used. `v := 1 − w`; the ring identity is packaged as a `noncomm_ring`
    `have` in the shape `−(a•u) + (a•u)·(1−w) = (1−w) − (1 − (1−a•u)·w)`, then `rw [hw]`,
    `sub_self`, `sub_zero` — this shape avoids any `nth_rewrite` on the two occurrences of
    `1 − w`. **Orientation confirmed at compile: `(a•u)*v = (a•u).comp v` is compactoid by
    `IsCompactoid.comp_right (hu.smul a) v`** (the ticket's `comp_left` guess was wrong;
    `comp_right` is correct).
  * `x + y − x·y = 0` likewise via `noncomm_ring` into `1 − (1−a•u)·w`, then `hw`, `sub_self`.
  * Final step `IsUnit.of_mul_eq_one _ hmul.symm` in `R` (commutative ⟹ Dedekind-finite).
  * Iff is the plain term `⟨isUnit_evalT_of_isUnit_one_sub_smul hu,
    isUnit_one_sub_smul_of_isUnit_evalT hu⟩`.
  **TRAP:** `isUnit_of_mul_eq_one` no longer exists in mathlib (see T016 note).

### [T018] The dichotomy: kernel at a finite-order zero
- **Status**: done — **File**: Riesz.lean — **Depends on**: T011, T012, T017 —
  **Type**: theorem
#### Statement
`exists_mem_ker_of_hasseDeriv_evalT`.
#### Proof sketch
1. `by_contra`: no nonzero kernel element ⟹ `Function.Injective (1 − a•u)` (linear:
   `sub_eq_zero` trick on images).
2. Obtain `N₀ … N_h` (T011). Induction `s < h`: `Nₛ = 0` — base: T012-zero +
   `h0 0` (note `hasseDeriv_zero`) gives `(1−a•u) * N₀ = 0`; injectivity pointwise
   ⟹ `N₀ = 0` (`ContinuousLinearMap.ext`); step: T012 at `s+1 ≤ h−1` with
   `h0 (s+1)` and `Nₛ = 0`.
3. At `s = h`: T012 gives `(1−a•u) * N_h = (ΔʰH)(a) • 1`; `hunit` ⟹ right inverse
   `hunit.unit⁻¹ • N_h`; two-sided via T011-commute; `IsUnit (1 − a•u)`.
4. T017(⟹) ⟹ `IsUnit (evalT a H)`; but `evalT a H = 0` (`h0 0` at `s = 0` with
   `hasseDeriv_zero`) and `¬IsUnit (0 : R)` (nontrivial `R` from `NormOneClass`:
   `‖1‖ = 1 ≠ 0 = ‖0‖` — `one_ne_zero` via `norm_one`; small glue). Contradiction.
#### Mathlib lemmas
`ContinuousLinearMap.ext`, `sub_eq_zero`, `isUnit_zero_iff`/`not_isUnit_zero`,
`one_ne_zero` derivation; T-outputs.
#### Sources
Serre §7 Prop. 12's mechanism + Buzzard p. 22's order definition (verbatim in
decomposition D3; the `h = 1` hand-trace recorded there).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new helper.
  Ran exactly as sketched. Shape notes:
  * `by_contra hcon` alone — **no `push_neg` needed** (and `push_neg` is deprecated in this
    mathlib): use `hcon ⟨y, hy0, hy⟩` directly against `¬ ∃ x, x ≠ 0 ∧ …`.
  * The usable form of injectivity is the operator statement
    `hMzero : ∀ M, (1 − a•u) * M = 0 → M = 0`, proved by `ContinuousLinearMap.ext` +
    `congrArg (fun T => T x)` + `simpa` (the simp set now has `mul_apply_eq_comp` and the
    root `zero_apply`; `ContinuousLinearMap.zero_apply`/`.mul_apply` are BOTH deprecated).
  * `choose N hN using fun s : ℕ => exists_isOpLimit_resolventPartialSum u hu a s` gives the
    whole family at once.
  * `hNs : ∀ s, s < h → N s = 0` by `intro s; induction s` (so the IH is
    `t < h → N t = 0`). In the successor branch `one_sub_smul_mul_resolventEval hu hs1
    (hN (t+1)) (hN t)` typechecks with NO index massage: the lemma wants
    `resolventPartialSum u a (t + 1 - 1)` and `t + 1 - 1` reduces to `t` definitionally
    (the usual `m + (t+1)` vs `m + t + 1` normal-form tax did NOT bite here).
  * Top equation at `s = h` uses `hN (h-1)` and `hNs (h-1) (by omega)` (omega uses `hh`).
  * `evalT a H = 0` from `h0 0` + `PowerSeries.hasseDeriv_zero`; nontriviality of `R` from
    `haveI : Nontrivial R := NormOneClass.nontrivial`, contradiction by `not_isUnit_zero`
    (no `one_ne_zero`/`norm_one` glue needed — `NormOneClass.nontrivial` is a direct term).

### CLEANUP-6 — /cleanup on Riesz.lean (T016–T018)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T016, T017, T018 — **Type**: cleanup

### [T019] Field input: finite order of vanishing (Weierstrass route)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T004, T005, T006 —
  **Parallel**: yes (independent of B/C/D clusters) — **Type**: theorem pair
#### Statement
`exists_factor_of_evalT_eq_zero`, `exists_order_of_evalT_eq_zero` (section `Order`).
#### Proof sketch
1. **Read `ForMathlib …/MulDistinguished.lean:35` first** and verify
   `IsMulDistinguished c (1 − C a⁻¹ * X) 1` at any `c > ‖a‖` (Gauss-dominant top:
   `‖a⁻¹‖·c > 1 = ‖1‖`; fields are `NormMulClass`). Set `c := ‖a‖ + 1`,
   `have : Fact (0 < c) := ⟨…⟩` (local instance — legitimate).
2. Package `f` at radius `c` (`hf c`), apply
   `weierstrassDivision_exists_of_isMulDistinguished`
   (`MulWeierstrassDivision.lean:343`): `f = ℓ*q + r`, `deg r < 1` ⟹ `r = C r₀`
   (`Polynomial.eq_C_of_degree_le_zero`). Evaluate at `a` (T004/T005 on the
   UNDERLYING raw series — cross the `Restricted` seam by `Subtype`-projections in
   term mode, never `rw` through it [repo seam convention]):
   `0 = f(a) = ℓ(a)·q(a) + r₀ = r₀`. Hence `f = ℓ * q.1` raw; `g := q.1` is
   restricted at every radius: at `c' ≥ c` from `q`'s membership… careful — `q` is
   restricted at `c` only; for `c' > c` REDO the division at `c'` and use uniqueness?
   Simpler: entirety of `g`: from `f = ℓ·g` solve coefficientwise
   (`g = Σ tail-sums`) OR divide at radius `c'` and compare by
   `weierstrassDivision_q_unique_of_isMulDistinguished` — both viable; recorded.
3. `exists_order`: first `a ≠ 0` (`evalT 0 f = coeff 0 f = 1 ≠ 0` vs `ha`).
   Define the iteration; termination: `‖·‖`-Gauss at radius `c`:
   `‖f‖ = ‖ℓ‖·‖g‖` (the `NormMulClass (Restricted K c)` instance,
   `MvPowerSeries/Restricted/GaussNorm.lean:269`), `‖ℓ‖ = c/‖a‖ > 1`
   (`norm_le_iff`/`norm_monomial` computations, `max`-form), constant coefficients:
   `coeff 0 g = 1` (from `f = ℓ·g`, `coeff_mul` at 0), so `1 ≤ ‖g‖`
   (`le_gaussNorm`): strong induction on `⌈log⌉`-free form — choose
   `h := ` the least `s` such that the `s`-th quotient does not vanish at `a`
   (exists: else `‖f‖ ≥ (c/‖a‖)ˢ·1 → ∞` contradicts fixed `‖f‖` — phrase as: the
   set of `s` with a factorisation `f = ℓˢ·gₛ` (all restricted, `coeff 0 gₛ = 1`) is
   bounded by `log‖f‖/log(c/‖a‖)`).
4. Convert to the `Δ`-form: with `f = ℓ^h * g`, `g(a) ≠ 0`: T006's pair
   (`b := a⁻¹`, `hba : a⁻¹ * a = 1` ✓ field) gives the `∀ s < h` vanishing and
   `evalT a (Δʰf) = (−a⁻¹)ʰ·g(a) ≠ 0` (field: product of nonzeros).
#### Mathlib/repo lemmas
`weierstrassDivision_exists_of_isMulDistinguished`,
`weierstrassDivision_q_unique_of_isMulDistinguished`,
`NormMulClass (Restricted K c)` instance, `le_gaussNorm`, `norm_le_iff`,
`Polynomial.eq_C_of_degree_le_zero`, `Fact.mk`, T004/T005/T006.
#### Sources
Buzzard p. 22 (verbatim in decomposition A4); termination is ours (recorded
deviation: replaces Buzzard's Noetherian-context argument; 5-line Gauss-norm
contradiction).
#### Generality
Field `K` (NontriviallyNormedField + ultrametric + complete). This ticket touches
ONLY the `PowerSeries` namespace part of the file.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change. Ran essentially as
  sketched; the two open questions in the sketch resolved as follows.
  * **"g entire" route: NEITHER (a) nor (b)** — the recorded routes (redo the division at
    each radius + `weierstrassDivision_q_unique_of_isMulDistinguished`, or coefficientwise
    tail sums) were both avoided. What lands is: divide at radius `c` for EVERY `c > ‖a‖`
    (private `exists_factor_isRestricted`), then identify the quotients obtained at two
    different radii by **cancelling the raw factor in `PowerSeries K`**. `mul_left_cancel₀`
    is NOT available (`IsLeftCancelMulZero K⟦X⟧` fails to synthesize — mathlib has no
    `IsDomain (PowerSeries R)` instance in scope here), so the cancellation is a 9-line
    private `eq_of_one_sub_C_mul_X_mul_eq` by coefficientwise induction reusing the
    file's `coeff_zero_/coeff_succ_one_sub_C_mul_X_mul`. Public shape:
    `g` at `c₀ = ‖a‖ + 1`; for an arbitrary `c > 0` divide at `max c (‖a‖+1)`, cancel to
    identify with `g`, then shrink the radius (`isRestricted_of_le`, a new private —
    ForMathlib has NO `IsRestricted` monotonicity lemma).
  * **Termination**: phrased as `pow_le_norm_of_eq_pow_mul` —
    `f = (1 - C a⁻¹X)^s · g`, `coeff 0 g = 1` ⟹ `(‖a‖⁻¹c)^s ≤ ‖f‖_c` at `c = ‖a‖ + 1`,
    proved in ONE line by `norm_mul` + `norm_pow` (the `NormMulClass`/`NormOneClass`
    instances on `Restricted K c`) — no induction. Then `pow_unbounded_of_one_lt` gives an
    `N` with `‖f‖_c < (‖a‖⁻¹c)^N`, and `Nat.find` on
    `¬ ∃ g, entire ∧ coeff 0 g = 1 ∧ f = ℓ^s·g` produces the order: `Nat.find ≠ 0` (as
    `P 0` holds with `g := f`), write it `k+1`, `Nat.find_min` gives `P k`, `Nat.find_spec`
    gives `¬P (k+1)`, and the division step at `g` would produce `P (k+1)` — so
    `evalT a g ≠ 0`. `1 ≤ k` because `k = 0` forces `g = f`.
  * **`Restricted` seam traps (important for T028 and anyone else touching `Restricted`)**:
    an inline `(⟨f, hf⟩ : Restricted K c)` UNFOLDS the opaque type to
    `↥(MvPowerSeries.IsRestricted.subring fun _ => c)` and then `Norm`/`HMul` fail to
    synthesize. Fix: a private `def restrictedOf (hf : IsRestricted c f) : Restricted K c`
    (the declared return type keeps it opaque at every use site). Everything else crosses
    the seam by term steps: `congrArg Subtype.val hfeq` gives the raw division equation
    directly (`(L*q + toRestricted r).1` is rfl-equal to `ℓ*q.1 + ↑r`), and
    `Subtype.ext hfg` lifts `f = ℓ^s·g` to `F = L^s * G` (so `(L^s*G).1 = L.1^s*G.1` IS rfl).
  * `IsMulDistinguished c (1 - C a⁻¹X) 1` verified exactly as sketched; `gaussNorm_eq` is
    discharged by `← Restricted.norm_def c` then a `le_antisymm` with
    `Restricted.norm_le_iff` / `Restricted.norm_coeff_mul_pow_le`. **All three take `c`
    EXPLICIT and FIRST** (same trap as `isRestricted.mul` etc.).
  * Remainder degree: `Nat.WithBot.lt_one_iff_le_zero.mp hrdeg` feeds
    `Polynomial.eq_C_of_degree_le_zero` with no cast massage; `conv_lhs => rw [...]` then
    `exact Polynomial.coe_C _` crosses to `PowerSeries`.
  * `h0 : coeff 0 f = 1` is genuinely unused in `exists_factor_of_evalT_eq_zero` (it is only
    needed by the ITERATION), so the declaration carries
    `set_option linter.unusedVariables false in` — which must sit BEFORE the docstring,
    not between docstring and `theorem` (parse error otherwise).
  * New privates (file-scoped, reusable by T028/T029): `isRestricted_of_le`, `evalT_zero`,
    `linFactor` + `val_linFactor` + `coeff_linFactor`, `restrictedOf` + `val_restrictedOf`,
    `one_lt_norm_inv_mul`, `norm_linFactor`, `isMulDistinguished_linFactor`,
    `exists_factor_isRestricted`, `eq_of_one_sub_C_mul_X_mul_eq`, `pow_le_norm_of_eq_pow_mul`.

### CLEANUP-ALL-1 — /cleanup-all pass on Riesz.lean before the milestone
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: CLEANUP-6, T019, CLEANUP-2 — **Type**: cleanup

### [T020] MILESTONE — the eigenvector theorems (field)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T017, T018, T019,
  CLEANUP-ALL-1 — **Type**: theorem ×3 (assembly)
#### Statement
`exists_eigenvector_of_evalT_charPowerSeries_eq_zero`,
`evalT_charPowerSeries_eq_zero_iff`,
`exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero`.
#### Proof sketch
1. Headline: `H := charPowerSeries u`; entirety (`charPowerSeries_isEntire`, needs
   `IsTate K` — instance from `NontriviallyNormedField`), `coeff 0 = 1`
   (`charCoeff_zero`); T019 gives `a ≠ 0` + order `h` (with `≠ 0 → IsUnit` in `K`:
   `Ne.isUnit`); T018 gives `x ≠ 0`, `(1−a•u)x = 0`; rearrange to `u x = a⁻¹ • x`
   (`smul_smul`, `inv_mul_cancel₀ ha0`, module algebra).
2. Iff: (→) is 1; (←): eigenvector ⟹ `(1−a•u) x = 0`, `x ≠ 0` ⟹ not injective ⟹
   `¬IsUnit (1−a•u)` (a unit CLM is injective — apply the inverse); T017-iff ⟹
   `¬IsUnit (evalT a H)` ⟹ `= 0` (field: `Ne.isUnit` contrapositive).
3. Conj: apply 1 to `w := φ∘v∘φ.symm`; transport `x` back by `φ.symm` (nonzero by
   injectivity; the eigen-equation by applying `φ.symm` and
   `ContinuousLinearEquiv.symm_apply_apply`, `map_smul`).
#### Mathlib lemmas
`Ne.isUnit`, `isUnit_iff_ne_zero`, `inv_mul_cancel₀`, `smul_smul`,
`ContinuousLinearEquiv` API, `charPowerSeries_conj` (`Fredholm.lean:960`),
`charPowerSeries_isEntire`, `charCoeff_zero`.
#### Sources
Serre Props. 11–12; Buzzard Prop. 3.2 + p. 32; decomposition D4–D6.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new helper,
  NO new import, NO new private. Ran exactly as sketched; all three proofs are short
  (15 / 21 / 8 lines) — the whole ticket is genuinely pure assembly of T017–T019.
  * **Headline**: `charPowerSeries_isEntire u hu` already has the shape
    `∀ C, 0 < C → IsRestricted C _` that T019 wants, so it is passed unapplied;
    `coeff 0 H = 1` is `rw [charPowerSeries_coeff, charCoeff_zero]`. T019 destructures as
    `⟨ha0, h, hh, h0, hne⟩` and `hne.isUnit` (`Ne.isUnit`, the `protected alias` half of
    `isUnit_iff_ne_zero`) feeds T018 directly. Rearrangement: `simpa using hx` turns
    `(1 - a•u) x = 0` into `x - a • u x = 0`, then `sub_eq_zero` + a 3-step `calc`
    (`inv_mul_cancel₀`, `smul_smul`).
  * **Iff (←)**: `hker : (1 - a•u) x = 0` by ONE `simp only [sub_apply, one_apply_eq_self,
    smul_apply, hx, smul_smul, mul_inv_cancel₀ ha0, one_smul, sub_self]`. Non-unit:
    `isUnit_iff_exists.1` gives the LEFT inverse `w` with `w * (1 - a•u) = 1`; applying it
    at `x` via `congrArg (fun T => T x)` + `simpa` (the file's existing idiom, cf. the T018
    proof) and then `rw [hker, map_zero]` yields `0 = x`. Finish: rewrite by T017's iff and
    `by_contra` + `Ne.isUnit` (deliberately NOT `push_neg`, which is deprecated).
  * **Conj**: `charPowerSeries_conj` was NOT needed — the statement is already phrased on
    the conjugate `w = φ ∘ v ∘ φ.symm`, so the headline applies verbatim with `_` for the
    operator. Transport is two `congrArg` + `simpa` steps (`φ` on `φ.symm y = 0` for
    nonzero-ness; `φ.symm` on the eigen-equation, `simp` discharging
    `symm_apply_apply` + `map_smul`).
  * **Trap confirmed**: `ContinuousLinearMap.sub_apply` / `.smul_apply` / `.one_apply` /
    `.mul_apply` are ALL deprecated (2026-05-20) in favour of the ROOT-level
    `sub_apply` / `smul_apply` / `one_apply_eq_self` / `mul_apply_eq_comp` (the
    `FunLike.IsApply` classes in `Mathlib/Data/FunLike/IsApply.lean`; `one_apply_eq_self` is
    `@[simp]`, so plain `simp` normalises `(1 : M →L M) x` on its own).
  * **Verification**: `lake build PhD.TateFredholm.Riesz` — 0 errors, 2322 jobs, 12 sorries
    left (all in `RieszDecomposition` / the T021–T030 extension). `#print axioms` on all
    three = `[propext, Classical.choice, Quot.sound]`.

### [T021] Serre's Riesz projectors
- **Status**: done — **File**: Riesz.lean — **Depends on**: T011, T012 — **Type**:
  theorem
#### Statement
`exists_rieszProjection` (section `RieszDecomposition`).
#### Proof sketch (Serre p. 81 verbatim transcription; quotes in decomposition P1)
1. Obtain `N₀ … N_h` (T011) and the equations (T012). Derive the chain
   `(1 - a•u)^(s+1) * N_s = 0` for `s < h` by induction (equations + commuting).
2. `c := hunit.unit`; `e := (↑c⁻¹ : R) • ((1 - a•u) * N_h)`,
   `f := -((↑c⁻¹ : R) • (u * N_{h-1}))`. From the `s = h` equation: `e + f = 1`.
   From the chain at `s = h-1`: `f * e^h = 0` (all factors commute — every operator
   in sight is a limit of polynomials in `u`, T011-commute + `Commute` closure).
3. Expand `1 = (e + f)^h` by `Commute.add_pow`; set `p := e^h`,
   `q := 1 - e^h` (= the binomial rest). `q * p = 0` termwise (each term of the rest
   carries an `f`; `f * e^h = 0`); hence `p * p = p` (`p = p(p+q)`).
4. Nilpotency: `(1 - a•u)^h * (1 - p) = 0`: each term of `q` contains `f`, and
   `(1 - a•u)^h * f = -(c⁻¹) • ((1 - a•u)^h * u * N_{h-1}) = 0` by the chain.
5. `w := ((↑c⁻¹ : R)^h) • ((1 - a•u)^(h-1) * N_h^h)`; then
   `(1 - a•u) * w = ((c⁻¹)^h) • ((1-a•u)^h * N_h^h) = e^h = p` ✓.
6. Commutation side-goals from T011-commute + `Commute.pow/smul/sub/one` closure.
#### Mathlib lemmas
`Commute.add_pow` (verify; fallback manual induction), `Commute` API,
`Units.smul`-arithmetic; T011/T012 outputs.
#### Sources
Serre p. 81 (verbatim, decomposition P1). Buzzard Prop. 3.2 p. 23 (ring-level check).
#### Generality
Over `R` Banach–Tate + order-`h` unit hypotheses — strictly generalises Serre's field
statement (matches Buzzard's Noetherian-Banach base and exceeds it).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new import.
  One new file-scoped private shared with T022/T023 (`apply_of_mul_eq`, see T022). Ran as
  sketched EXCEPT for one deliberate simplification that removes the binomial expansion
  entirely.
  * **`Commute.add_pow` was NOT needed.** Since `e + f = 1` gives `f = 1 - e`, Serre's
    "développer `(e+f)ʰ = 1`" collapses: `f·eʰ = 0` reads `(1-e)eʰ = 0`, i.e.
    `e^{h+1} = eʰ`; a 3-line induction gives `e^{h+k} = eʰ` for all `k`, so
    `eʰ·eʰ = e^{h+h} = eʰ`. This also sidesteps the fact that `Commute (N h) (N (h-1))` is
    NOT available from T011 (T011 only gives `Commute u (N s)`) — the binomial route would
    have needed it, or a `f = 1 - e` rewrite anyway. **Recorded as a plan simplification.**
  * Nilpotency likewise avoids `geom_sum`: `∀ k, bʰ(1 - eᵏ) = 0` by induction with
    `1 - e^{j+1} = (1 - eʲ) + eʲ(1 - e)` and `bʰ(1-e) = 0`, using `Commute b e`.
  * **Skeleton of the proof**: `choose N hN`; `set b := 1 - a•u with hbdef` (invoking T012
    under `set` needs `rw [hbdef]` first — `set` does not fold new terms); chain
    `hchain : ∀ s < h, b^{s+1} * N s = 0` by induction (T012 + `(hbu.pow_left _).eq`);
    `d := (ΔʰH)(a)`, `di := ↑hunit.unit⁻¹`, `hdi : di * d = 1` (`IsUnit.val_inv_mul`);
    `e := di • (b * N h)`; `hE : e = di • (u * N (h-1)) + 1` from T012 at `s = h`;
    `hone_sub_e : 1 - e = -(di • (u * N (h-1)))` (`abel`); `hM'chain : bʰ * N (h-1) = 0`
    (chain at `h-1`, `Nat.sub_add_cancel hh`); `hbf : bʰ(1-e) = 0`; `heh : eʰ = diʰ • (bʰ Nₕʰ)`
    (`smul_pow` + `Commute.mul_pow`); `hfe : (1-e)eʰ = 0`; idempotency; nilpotency;
    witness `w := diʰ • (b^{h-1} Nₕʰ)` with `b * w = eʰ` (`← pow_succ'`,
    `Nat.sub_add_cancel hh`).
  * **Commutation conjuncts** are one-liners in the `Commute` closure API:
    `Commute.one_left/.sub_left/.smul_left/.smul_right/.mul_left/.mul_right/.pow_left/`
    `.pow_right/.pow_pow/.mul_pow/.eq`. `smul_pow` and `Commute.smul_left/right` both exist
    for `R` acting on `c(I,R) →L[R] c(I,R)` (verified).
  * **Trap**: `(huw : Commute u w)` type-ascription does NOT enable dot notation —
    `Commute` unfolds to `Eq`, so `(huw : Commute u w).smul_left a` fails with
    `Eq.smul_left`. Bind it first: `have hcuw : Commute u w := huw`.
  * **Trap**: `c` is a terrible local name in this file (`c(I, R)` notation); used `d`/`di`.

### [T022] Kernel/range characterisations and the topological complement
- **Status**: done — **File**: Riesz.lean — **Depends on**: T021 (shape only; provable
  standalone from its hypotheses) — **Type**: lemma triple
#### Statement
`ker_one_sub_smul_pow_of_rieszProjection`, `range_one_sub_smul_pow_of_rieszProjection`,
`isTopCompl_range_one_sub_range_of_isIdempotent`.
#### Proof sketch
1. Key identity: `p ^ h = ((1 - a•u) * w)^h = (1 - a•u)^h * w^h` (commuting), and
   `p ^ h = p` (idempotent, `1 ≤ h` — for the `IsTopCompl` lemma no `h` is needed).
2. `ker ψ = range (1 - p)` (`ψ := (1 - a•u)^h`): (⊇) `ψ * (1 - p) = 0` applied
   pointwise; (⊆) `x ∈ ker ψ` ⟹ `p x = (ψ * w^h) x = w^h (ψ x) = 0` (commuting) ⟹
   `x = (1-p) x ∈ range (1-p)`.
3. `range ψ = range p`: (⊆) `ψ = ψ * (p + (1-p)) = ψ * p` + `ψ*p = p*ψ` ⟹
   `ψ x = p (ψ x)`; (⊇) `p = ψ * w^h` ⟹ `p x = ψ (w^h x)`.
4. `IsTopCompl`: `(1-p)` is idempotent (`IsIdempotentElem.one_sub`);
   `ContinuousLinearMap.IsIdempotentElem.isTopCompl` gives
   `IsTopCompl (1-p).range (1-p).ker`; convert `(1-p).ker = p.range` (idempotent
   ker/range swap — mathlib `IsIdempotentElem` CLM lemmas in
   `Topology/Algebra/Module/ContinuousLinearMap/Idempotent.lean`, worker greps; else
   3-line double-inclusion).
#### Mathlib lemmas
`ContinuousLinearMap.IsIdempotentElem.isTopCompl` (verified present),
`IsIdempotentElem.one_sub`, `Submodule.IsTopCompl.isClosed` (for downstream use).
#### Sources
Buzzard p. 23 ("N = ker(ψ) and F = Im(ψ)"); Serre p. 81. Decomposition P2.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new import.
  Ran exactly as sketched; the three proofs are 22 / 25 / 14 lines.
  * **ONE new file-scoped private** (placed at the top of `RieszDecomposition`, used by all
    of T022/T023): `apply_of_mul_eq {A B C} (hABC : A * B = C) (x) : A (B x) = C x`
    (`congrArg (fun T => T x)` + `simpa`). Needed because the deprecation of
    `ContinuousLinearMap.mul_apply` makes that idiom recur ~8 times.
  * `p ^ h = p` is proved WITHOUT `1 ≤ h`: for `h = 0`, `hnil` reads `1·(1-p) = 0`, so
    `p = 1 = p⁰`; for `h = k+1` it is `IsIdempotentElem.pow_succ_eq k hp` (signature:
    `(n : ℕ) (h : IsIdempotentElem p) : p ^ (n+1) = p`). So the two characterisations hold
    at every `h`, which is exactly what T023 needs.
  * `ker`: `w^h * (1-a•u)^h = p` via `Commute.pow_pow` + `Commute.mul_pow` + `hw` + `p^h = p`.
  * `range`: `hnil` rearranges (`mul_sub`, `mul_one`, `sub_eq_zero`) to `ψ * p = ψ`, then
    `Commute.pow_left` gives `p * ψ = ψ`; both inclusions are then `exact ⟨_, apply_of_mul_eq …⟩`.
  * **Trap**: `simpa using (congrArg … )` FAILS on range/ker membership goals — `simp`
    normalises `((1 - a•u)^h) y` to `(⇑(1 - a•u))^[h] y` on one side and to a
    `LinearMap`-power `((1 - a•↑u)^h) y` on the other, so the two sides diverge. Use the
    `apply_of_mul_eq` term and `exact ⟨_, …⟩` (defeq through `ContinuousLinearMap.coe_coe`).
  * `isTopCompl`: `ContinuousLinearMap.IsIdempotentElem.isTopCompl` applied to
    `(hp : IsIdempotentElem p).one_sub` gives `IsTopCompl (1-p).range (1-p).ker`; the
    ker/range swap `(1-p).ker = p.range` is the advertised 3-line double inclusion (no
    CLM-level mathlib lemma exists; `LinearMap.IsIdempotentElem.ker_eq_range_one_sub` in
    `Mathlib/LinearAlgebra/Projection.lean` is the `LinearMap` analogue and would need
    coe-juggling, so it was not used).
  * **Trap**: `IsIdempotentElem` is a `def` unfolding to `Eq`, so `h2.isTopCompl` fails
    (`Eq.isTopCompl`); must write `ContinuousLinearMap.IsIdempotentElem.isTopCompl h2`.

### [T023] Uniqueness of the Riesz projector
- **Status**: done — **File**: Riesz.lean — **Depends on**: T022 — **Type**: theorem
#### Statement
`rieszProjection_unique`.
#### Proof sketch
1. By T022 at order `h` and at order `h'`: both `range (1-p) = ker ψ^{max}`-free:
   apply the `ker`-characterisation for `p` at exponent `h` and for `p'` at `h'`;
   upgrade both to the common exponent `h + h'` (the characterisation proof works for
   any exponent `≥` the given one — apply T022 with `hnil` weakened by multiplying:
   `(1-a•u)^(h+k) * (1-p) = (1-a•u)^k * 0 = 0`, and `w`-powers likewise) so
   `range (1-p) = ker (1-a•u)^(h+h') = range (1-p')` and dually
   `range p = range p'`.
2. Two idempotents with equal ranges and equal complement-ranges are equal,
   pointwise: `p' x = p' (p x) + p' ((1-p) x)`; `p x ∈ range p = range p'` and `p'`
   fixes its range (`p' (p' y) = p' y`); `(1-p) x ∈ range (1-p) = range (1-p') =
   ker p'` (idempotent swap). Hence `p' x = p x`.  (No commuting between `p` and
   `p'` is used — decomposition P3's repaired argument.)
#### Sources
Serre p. 81 ("son unicité est immédiate"); Buzzard p. 23. Decomposition P3 (attack
log records the repaired idempotent-equality argument).
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new private.
  33 lines, exactly the sketch. **Decomposition P3's REPAIRED argument WAS needed as
  written and was used verbatim** — `p` and `p'` genuinely do not commute here, and the
  proof never asks them to.
  * Step 1 (common exponent) is 4 lines: `(1-a•u)^{h+h'}(1-p) = 0` by
    `rw [add_comm, pow_add, mul_assoc, hnil, mul_zero]` and the primed version by
    `rw [pow_add, mul_assoc, hnil', mul_zero]`. Then T022 is applied FOUR times with
    `(h := h + h')`. **`hw`/`huw`/`hp`/`hup`/`hpw` are exponent-free**, so nothing else
    has to be upgraded — this is why the T022 statements were worth keeping `h`-generic.
  * Step 2 (pointwise): `ContinuousLinearMap.ext`; `p x ∈ range p = range p'` gives
    `p x = p' y`, so `p' (p x) = p'(p' y) = p' y = p x` (`apply_of_mul_eq hp' y`);
    `(1-p) x ∈ range (1-p) = range (1-p')` gives `(1-p) x = (1-p') z`, so
    `p' ((1-p) x) = (p' * (1-p')) z = 0` (`apply_of_mul_eq hzero z`, `hzero` by
    `mul_sub, mul_one, hp', sub_self`). Then `p' x = p'(p x) + p'((1-p) x) = p x`.
  * `hh`/`hh'` turn out to be UNUSED (the T022 characterisations hold at every exponent,
    see T022's note) — the hypotheses are kept because the statement is fenced.
  * Membership terms `hR ▸ ⟨x, rfl⟩` typecheck directly (`⟨x, rfl⟩ : p x ∈ p.range` is
    defeq through `ContinuousLinearMap.coe_coe`).

### CLEANUP-7 — /cleanup on Riesz.lean (T021–T023)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T021, T022, T023 — **Type**: cleanup

### [T024] `N(a)` is finite-dimensional (field)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T021, T022 — **Type**:
  theorem
#### Statement
`finite_ker_one_sub_smul_pow` (section `Field`).
#### Proof sketch (Buzzard p. 23's argument, run directly on the closed subspace)
1. `N := ψ.ker` closed (continuous) ⟹ `CompleteSpace N`; instances for the
   `OperatorNorm` framework on `N` (induced norm; `IsBoundedSMul` restriction).
2. On `N`: `(1 - a•u)` compresses to a nilpotent `ν` (T022 ker-characterisation:
   `ψ x = 0` and stability `u(N) ⊆ N` from commuting); `(a•u)|_N = 1 - ν` is
   invertible with polynomial inverse `Σ_{k<h} ν^k`; hence
   `1_N = ((a•u)|_N) * Σ ν^k`.
3. `u|_N` is completely continuous: finite-rank `v → u` (from
   `hu.isCompletelyContinuous`, `Matrix.lean:418`) compress along
   `ι : N →L c(I,K)` (inclusion) and a continuous retraction… no retraction needed:
   `IsCompletelyContinuous (u|_N)` directly: `‖(u - v)|_N‖ ≤ ‖u - v‖` (restriction
   norm-decreasing for the induced norm) and `v|_N`-corestricted?? — corestriction
   target must be `N`: use instead the operator `π_N ∘ v ∘ ι` where
   `π_N := (1-p)` corestricted to `N` (continuous, from T021's `p`; `(1-p)`
   restricted to `N` is the identity): `‖u|_N − π_N v ι‖ ≤ ‖1-p‖·‖u − v‖`-bound +
   `IsFiniteRank (π_N ∘ v ∘ ι)` (`IsFiniteRank.comp_left/right`,
   `Compact.lean:43,51`).
4. `1_N` completely continuous (product with bounded, step 2 + 3,
   `IsCompletelyContinuous.comp_left`); choose finite-rank `α`, `‖1_N - α‖ < 1`;
   Neumann `exists_inverse_of_norm_id_sub_lt_one` ⟹ `α` invertible ⟹
   `id = α ∘ α⁻¹`… `range (1_N) ⊆` f.g. submodule (from `IsFiniteRank α` +
   invertibility: `range α⁻¹ ∘ α`-argument) ⟹ `Module.Finite K N`
   (`Module.Finite.iff_fg`, field).
#### Mathlib/repo lemmas
`IsCompactoid.isCompletelyContinuous`, `IsFiniteRank.comp_left/right`,
`IsCompletelyContinuous.comp_left`, `exists_inverse_of_norm_id_sub_lt_one`,
`Module.Finite.iff_fg`, `Submodule.ClosedComplemented`-free.
**Do NOT route through `Pr.lean`'s `finite_projective_of_one_sub_compact_nilpotent`**
— its `HasPr` index-set convention has a cardinality obstruction for small `N`
(decomposition P4, successful attack recorded).
#### Sources
Buzzard p. 23 (verbatim in decomposition P4); Serre p. 81.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new private
  (reuses T021's `apply_of_mul_eq`). 68 lines, exactly the sketch; `Pr.lean` untouched, so
  P4's recorded `HasPr` cardinality obstruction is confirmed avoided.
  * Instances on `N := ψ.ker`: `NormedAddCommGroup ↥N` and `Module K ↥N` are found
    (`Submodule.normedAddCommGroup`); `CompleteSpace ↥N` is
    `ψ.isClosed_ker.completeSpace_coe`; **`IsBoundedSMul K ↥N` is NOT an instance** and
    must be supplied by hand — `haveI := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le r (x : c(I, K))` (works because `Submodule.coe_norm` is `rfl`).
  * Compression: `ι := N.subtypeL`, `π := (1-p).codRestrict N hmemN` (uses T022's
    `ker ψ = range (1-p)`), and one reusable lemma
    `hcoe : (∀ x ∈ N, T x ∈ N) → ↑((π ∘SL T ∘SL ι) y) = T ↑y` — proved from
    `hfix : ∀ x ∈ N, (1-p) x = x` (idempotence of `1-p`, i.e. `apply_of_mul_eq hidem`).
    Everything downstream (`ν`, `τ`, powers, sums) is then coordinate bookkeeping on `↑`.
  * `N`-stability: `1 - a•u` from `ψ * (1-a•u) = (1-a•u) * ψ` (`← pow_succ, ← pow_succ'`);
    `a•u` from `(a•u) x = x - (1-a•u) x` plus `Submodule.sub_mem`.
  * `1_N = τ * ∑_{k<h} ν^k` uses **`mul_neg_geom_sum`** (`Mathlib/Algebra/Ring/GeomSum.lean`,
    `Ring` section — valid in the *non-commutative* endomorphism ring). **Trap**: the
    `← neg_sub` + `neg_mul` + `mul_geom_sum` route of `OperatorNorm.lean:581` does NOT
    replay here — `rw [neg_mul]` fails to match `-(ν - 1) * S`.
  * `(ν^(j+1)) y = ν ((ν^j) y)` is `by rw [pow_succ']; rfl` (no `simpa using congrArg`,
    per T022's trap); `ν^h = 0` is `Subtype.ext` + `y.2`.
  * Endgame: `honecc 1 one_pos` → finite-rank `α` with `‖1 - α‖ < 1`;
    `exists_inverse_of_norm_id_sub_lt_one α (by rwa [← ContinuousLinearMap.one_def])`;
    `hv1 ▸ hαfr.comp_right v : IsFiniteRank (id)`; `top_le_iff.mp fun x _ => hQle ⟨x, rfl⟩`
    gives `Q = ⊤`, and `Module.Finite` is the anonymous constructor `⟨hQtop ▸ hQfg⟩`.

### [T025] Nilpotent block determinant
- **Status**: done — **File**: Riesz.lean — **Depends on**: none — **Parallel**: yes —
  **Type**: lemma
#### Statement
`det_one_sub_X_smul_of_isNilpotent` (section `Field`).
#### Proof sketch
1. Write `1 - X•(A.map C) = (1 - C a⁻¹ * X)•1 + (C a⁻¹ * X)•(1 - a•A).map C`-shape
   identity (check: `(1-Ca⁻¹X)·1 + Ca⁻¹X·(1 - aA) = 1 - Ca⁻¹X·aA = 1 - X·A` using
   `a⁻¹a = 1` ✓).
2. `det` of `unit·(1 + nilpotent-multiple)`: over the commutative ring
   `Polynomial K` localised: cleanest concrete route — `det (1 + M) = 1` for
   nilpotent `M` (classical; search `Matrix.det_one_add_of_isNilpotent` /
   `IsNilpotent.det_one_add`; if absent, prove via `Matrix.det`-of-unipotent:
   `1 + M = exp`-free: use the fact that `det(1 + M) - 1` is nilpotent AND
   idempotent-free… robust elementary route: over the field of fractions
   `K(X)`, `1 + M` is conjugate-to-triangular… avoid; better: coefficient argument —
   `det (1 - X•A)` and the factorisation forced by the Cayley–Hamilton/charpoly of
   `A = a⁻¹(1 - N)`: `Matrix.charpoly` of `A`: eigenvalue-free statement
   `A.charpoly = (X - C a⁻¹)^n` from `IsNilpotent (a⁻¹•1 - A)`?? mathlib:
   `Matrix.charpoly_of_isNilpotent`-search (`IsNilpotent.charpoly` exists for
   nilpotent: `charpoly = X^n` — then shift by scalar:
   `Matrix.charpoly_sub_scalar`-type: `(A - c•1).charpoly (X) = A.charpoly (X + c)`
   — `Matrix.charpoly_add_scalar`?? worker greps; this is the intended route);
   convert `charpoly` (`det (X•1 - A)`) to our `det (1 - X•A)` by the standard
   reversal `det(1 - X A) = X^n·charpoly-reversal` — the reversal bookkeeping is
   the fiddly part; ~60-100 LOC.
#### Mathlib lemmas
`Matrix.charpoly`, `IsNilpotent.charpoly` (verify name), `Matrix.det_smul`,
reversal lemmas (`Polynomial.reverse`-free manual route acceptable).
#### Sources
Serre p. 81 ("det(1 − tu_W) = (1 − ta⁻¹)^{dim W}"). Decomposition Q2.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new private,
  NO new import, 33 lines. **The sketched `charpoly`-reversal route was NOT used — the
  reversal bookkeeping is entirely avoidable.** Route that worked (charpoly *evaluated*,
  not reversed):
  1. `B := A - a⁻¹•1 = (-a⁻¹) • (1 - a•A)` is nilpotent (the identity closes by
     `rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ ha]` then **`module`**);
     `IsNilpotent (r • M)` is `⟨k, by rw [smul_pow, hk, smul_zero]⟩`.
  2. `M := X • B.map C` is nilpotent over `K[X]`; the power step is
     `rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]` then
     `Matrix.map_zero _ (map_zero _)`.
  3. `M.charpoly = X ^ n`: `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`
     (`Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:361`) + `Fintype.card_fin` +
     `IsNilpotent.eq_zero` — the last step is where **`IsReduced K[X][X]` (a domain)** is
     used; the fact is FALSE over a general commutative ring (`ℤ/4`, `M = (2)`), which is
     why the statement is fenced to a field.
  4. `1 - X•A.map C = Matrix.scalar (Fin n) (1 - C a⁻¹ * X) - M` (entrywise,
     `by_cases i = j <;> simp [...]; ring`), then **`Matrix.eval_charpoly`**
     (`Charpoly/Basic.lean:135`: `M.charpoly.eval t = (scalar _ t - M).det`) turns the goal
     into `eval (1 - C a⁻¹ X) (X ^ n)`.
  * Bonus fact verified: our LHS is *definitionally* `Matrix.charpolyRev A`.
  * No extra import needed — `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` already comes in
    through `Fredholm.lean`.

### [T026] Block-triangular factorisation of the determinant (Serre Lemme 2)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T002 — **Parallel**: yes —
  **Type**: lemma pair
#### Statement
`isCompactoid_of_comp_embedding`, `charPowerSeries_blockTriangular` (section
`RieszDecomposition`).
#### Proof sketch
1. Embedding lemma: `rowNorm v j ≤ rowNorm u (e j)` (iSup over a sub-family along
   the injection `e`… careful: `rowNorm v j = ⨆ i, ‖matrixCoeff u (e j) (e i)‖ ≤
   rowNorm u (e j)` — `Real.iSup_le` + `le_ciSup`); compactoid: cofinite-null
   composed with an injection stays cofinite-null
   (`Function.Injective.tendsto_cofinite`? worker greps
   `Filter.Tendsto.comp` + `Function.Injective.comap_cofinite_eq`? — mathlib has
   `Function.Injective.comap_cofinite_eq : comap e cofinite = cofinite`).
2. Minor factorisation: for `S : Finset I`, if `S` meets both blocks, reindex
   `S ≃ (S ∩ P) ⊕ (S ∩ ¬P)`-subtypes; the triangularity makes the matrix
   `fromBlocks`-triangular; `Matrix.det_fromBlocks_zero₂₁` (verify orientation —
   `zero₁₂`?) ⟹ `minor u S = minor u₁ (S∩P) * minor u₂ (S∩¬P)` (through `h₁ h₂`
   coefficient-matching and `Matrix.det_reindex_self`).
3. `charCoeff` convolution: `cₙ(u) = Σ' S : card n, …` — split the tsum over the
   bijection `{S // card = n} ≃ Σ (k ≤ n), {S₁ // card = k} × {S₂ // card = n-k}`
   (S ↦ (S∩P, S∩¬P)); `Summable.tsum_sigma`/`tsum_prod` (summability from
   `summable_minor` for `u₁, u₂` via step-1 compactoidness); signs:
   `(-1)^n = (-1)^k·(-1)^(n-k)`; conclude `coeff`-wise against
   `PowerSeries.coeff_mul` (antidiagonal).
#### Mathlib lemmas
`Matrix.det_fromBlocks_zero₂₁`/`zero₁₂`, `Matrix.det_reindex_self`,
`Summable.tsum_prod`/`tsum_sigma`, `Function.Injective.comap_cofinite_eq`,
`Finset.card` splitting API, `PowerSeries.coeff_mul`.
#### Sources
Serre p. 77, Lemme 2 (verbatim in decomposition Q3). Jacobs' equivalent is OFF-LIMITS
(other board's file) — independent proof.
- **Progress** (2026-08-04, sorry-free, std axioms): NO signature change, NO new import.
  **Five new file-scoped privates** (all in `RieszDecomposition`, all `I`-only, no `R`):
  `blockEquiv`, `card_blockEquiv`, `fiberEquiv`, `blockCard`, `blockCardFiberEquiv`.
  Embedding lemma = 8 lines; the block factorisation = 92 lines.
  * `isCompactoid_of_comp_embedding`: `rowNorm v j ≤ rowNorm u (e j)` by
    `Real.iSup_le` + the private `norm_matrixCoeff_le_rowNorm'`, then
    `squeeze_zero _ hdom (hu.comp e.injective.tendsto_cofinite)` —
    **`Function.Injective.tendsto_cofinite` exists** (`Order/Filter/Cofinite.lean:256`), so
    `Function.Injective.comap_cofinite_eq` was not needed.
  * Minor factorisation: **`Matrix.twoBlockTriangular_det`**
    (`Mathlib/LinearAlgebra/Matrix/Block.lean:267`, already imported via `Fredholm.lean`) does
    the whole job on the *subtype-indexed* blocks `Matrix.toSquareBlockProp` — no manual
    `fromBlocks` reindexing. Its hypothesis `∀ i, ¬p i → ∀ j, p j → M i j = 0` matches
    `htri` argument-for-argument. **Orientation answer: `det_fromBlocks_zero₂₁` is the right
    one** (it is exactly what `twoBlockTriangular_det` uses internally).
    Bridging `{x : ↥S // P ↑x}` ↔ `↥(S.subtype P)` is `fiberEquiv` (both `left_inv`/
    `right_inv` are `rfl`) plus `Matrix.det_submatrix_equiv_self`; the entry check needs
    `rw [Matrix.submatrix_apply, Matrix.of_apply, h₁ (e j) (e i)]` **followed by `rfl`** —
    `exact (h₁ _ _).symm` cannot solve it (metavariables in projection position).
  * `Finset` bookkeeping: `blockEquiv : Finset I ≃ Finset {i // P i} × Finset {i // ¬P i}`
    (`subtype`/`map ∪ map`); `card_blockEquiv` is `Finset.card_subtype` +
    **`Finset.card_filter_add_card_filter_not`** (the guessed
    `filter_card_add_filter_neg_card_eq_card` does not exist).
  * `tsum` Fubini: the sigma-over-antidiagonal was AVOIDED. Instead:
    `Equiv.subtypeEquiv (blockEquiv P).symm` transports `summable_minor u hu n` to the
    *pair* index type; then **`HasSum.tsum_fiberwise`**
    (`InfiniteSum/Constructions.lean`, additive form of `HasProd.tprod_fiberwise`) over the
    **Fintype** base `↥(Finset.antidiagonal n)` via `blockCard`, `hasSum_fintype` +
    `HasSum.unique`, and `Finset.sum_coe_sort` at the end. Each fibre is
    `blockCardFiberEquiv` (again `left_inv`/`right_inv` = `rfl`) + `Summable.tsum_mul_tsum`.
  * **Trap (new, costly)**: applying the private
    `PowerSeries.summable_mul_of_tendsto_cofinite` (conclusion
    `Summable fun x : ι × κ => F x.1 * G x.2`) against a goal whose two index types are
    *different* makes the unifier unfold `Finset.sum → Multiset.foldr → List.map` and blow
    past 1e6 heartbeats (confirmed with `set_option diagnostics true`; giving `F`/`G`
    explicitly does NOT help). Fix: `(… ).congr fun _ => rfl` — `Summable.congr` fixes `g`
    from the goal and only ever checks a pointwise `rfl`. Same shape is likely to bite
    anywhere two distinct index types meet a product-summability lemma.
  * `Summable.tendsto_cofinite_zero` supplies the cofinite hypotheses from `summable_minor`.
  * Signs: `charCoeff u₁ k * charCoeff u₂ l = (-1)^(k+l) * (…)` by `← hq, pow_add; ring`
    against `PowerSeries.coeff_mul`'s antidiagonal.
  * `Finset.sum_coe_sort` must be given **both** explicit arguments (the summand's
    dependence on `↑p` sits in a *type*, so `∑ i, ?f ↑i` does not higher-order-match).

### CLEANUP-8 — /cleanup on Riesz.lean (T024–T026)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T024, T025, T026 — **Type**: cleanup

### [T027] Order uniqueness
- **Status**: done — **File**: Riesz.lean — **Depends on**: T003, T004 — **Parallel**:
  yes — **Type**: lemma
#### Statement
`hasseDeriv_order_unique` (section `Order`).
#### Proof sketch
`rcases lt_trichotomy h h'`: if `h < h'` then `h0' h h.lt` contradicts `hh`;
symmetric; middle case done. Two lines.
#### Sources
Decomposition Q1.
- **Progress** (2026-08-04, sorry-free, std axioms): exactly the sketch, 4 lines —
  `rcases lt_trichotomy h h' with hlt | heq | hgt` then `absurd (h0' h hlt) hh` / `heq` /
  `absurd (h0 h' hgt) hh'`. No `omega`, no helper.

### [T028] The factorisation `H = (1−a⁻¹T)^d · H'` (block conjugation)
- **Status**: done — **File**: Riesz.lean — **Depends on**: T017, T018, T021, T022,
  T024, T025, T026 — **Type**: theorem (the chunkiest of the extension)
#### Statement
`charPowerSeries_eq_pow_mul_of_riesz` (section `Field`).
#### Proof sketch (decomposition Q4; each link verified there)
1. `d ≥ 1`: T018 supplies a kernel element, so `N := ψ.ker ≠ ⊥` (with T024:
   `0 < finrank = d`).
2. Basis of `N` (T024 + field) ⟹ `eN : N ≃L[K] c(Fin d, K)` (finite-dimensional
   continuity: `LinearMap.continuous_of_finiteDimensional`; the model space on
   `Fin d` is just `Fin d → K` with sup — small bridging equiv).
3. `F := p.range` with `IsTopCompl` (T022): `F` closed ⟹ Banach;
   `isPotentiallyONable_of_uniformizer hd` ⟹ `eF : F ≃L[K] c(s, K)`.
4. Glue: `Submodule.prodEquivOfIsTopCompl` (mathlib, imported) + local lemma
   `c(A, K) × c(B, K) ≃L[K] c(A ⊕ B, K)` (coordinates; `Sum.elim`) ⟹
   `Φ : c(Fin d ⊕ s, K) ≃L[K] c(I, K)` carrying the blocks to `N, F`.
5. Conjugate: `u' := Φ.symm ∘ u ∘ Φ`; `charPowerSeries_conj`
   (`Fredholm.lean:960`) ⟹ same char series; `u'` block-DIAGONAL (both parts
   stable: `N` by `ψ`-commuting, `F` by `p`-commuting) ⟹
   `charPowerSeries_blockTriangular` (T026, with `P := Sum.isLeft`) ⟹
   `H = H_N · H_F`.
6. `H_N`: the `Fin d`-block has `1 - a•(block)` nilpotent (T022 ker-char through
   `Φ`) ⟹ T025 ⟹ `H_N = (1 - C a⁻¹ X)^d` (via `charCoeff_eq_det_coeff` to identify
   the finite char series with the det polynomial).
7. `H_F := H'`: entire (`charPowerSeries_isEntire`, block compactoid via T026's
   embedding lemma + conj-transport `isCompactoid`… conj of compactoid: through
   `Φ` — `matrixCoeff`-transport; worker may need a small conj-compactoid lemma —
   `BaseChange.lean:393`'s `isCompactoid_map_equiv` is for ring maps, not conj;
   state privately); `evalT a H' ≠ 0`: `1 - a•(F-block)` invertible (the `w` of
   T021 compressed to `F`, through `Φ`) + T017(⟹) ⟹ `IsUnit` ⟹ `≠ 0`.
#### Mathlib/repo lemmas
`isPotentiallyONable_of_uniformizer` (`BaseChange.lean:609`),
`Submodule.prodEquivOfIsTopCompl`, `LinearMap.continuous_of_finiteDimensional`,
`charPowerSeries_conj`, T017/T021/T022/T024/T025/T026.
#### Sources
Serre p. 81 (verbatim in decomposition Q4, with the `d ≥ 1` attack recorded).
- **Progress** (2026-08-05, sorry-free, std axioms): NO signature change. 228-line proof,
  following the Q4 sketch link for link. Two new imports on the file:
  `PhD.TateFredholm.BaseChange` (for `isPotentiallyONable_of_uniformizer`; no cycle — nothing
  imports `Riesz`) and `Mathlib.Topology.Algebra.Module.FiniteDimension` (for
  `LinearEquiv.toContinuousLinearEquiv`). Eight new file-scoped privates:
  `conjRingEquiv` (+ `_apply`, `_eq_comp`, `_one_sub_smul`), `reindexCLE_apply'`,
  `reindexCLE_symm_single`, `sumIsLeftEquiv`, `sumIsRightEquiv`.
  * **The organising idea that made it tractable**: package conjugation
    `T ↦ e ∘ T ∘ e⁻¹` as a **`RingEquiv`** (`conjRingEquiv`). Then `map_pow` +
    `map_zero` transport the nilpotency of `1 − a·u|_N` to the `Fin d` block, and
    `IsUnit.map` transports the invertibility of `1 − a·u|_F` to the `s` block, with no
    hand-rolled conjugation algebra anywhere. Only the `1 − a•T` combination needs a
    bespoke lemma (`conjRingEquiv_one_sub_smul`, one `ext` + `simp`) since `RingEquiv`
    knows nothing about the `K`-action.
  * **`d ≥ 1` turned out NOT to be load-bearing** (the Q4 attack over-worried). The vacuity
    the attack feared cannot arise on this route: `H'` is produced as `charPowerSeries u₂`
    of the `F`-block and its non-vanishing comes from T017 applied to *that block*, which is
    valid for every `d` including `0`. Nothing in the proof needs `N ≠ ⊥`, so T018 is not
    used at all. (`a ≠ 0` — which *is* needed, for T025 — comes from `h0 0` + T019, not
    from T018.) Recorded here so the next reader does not re-add dead code.
  * **Hardest point** (two elaborator blow-ups, both around the conjugation seam):
    (i) `exact (charPowerSeries_conj … ).trans …` against a goal stated with
    `conjRingEquiv` sent the unifier into `whnf` on `charPowerSeries` (a `tsum` of minors)
    and blew 1e6 heartbeats. Fix: never let `exact` bridge that defeq — discharge it once
    at *operator* level with the `rfl`-lemma `conjRingEquiv_eq_comp` and then `rw`.
    (ii) writing the composite inline as
    `(reindexCLE eL : c(Fin d, K) →L[K] c(…, K)).comp v` inside a `show … from rfl` left the
    coercions as metavariables; the standalone `conjRingEquiv_eq_comp` (stated in a section
    where `E`, `E'` are variables) elaborates cleanly and is the fix for that too.
  * **`NormedSpace` diamond (new trap)**: `NormedSpace K c(I, K)` is NOT an instance (the
    development is stated with `IsBoundedSMul`), and `isPotentiallyONable_of_uniformizer`
    demands it. Supplying it as `haveI : NormedSpace K c(I,K) := ⟨fun r x => norm_smul_le r x⟩`
    **breaks** the downstream `Submodule.normedSpace`, because the anonymous constructor
    creates a *second* `Module K c(I,K)` and then `IsScalarTower K K c(I,K)` fails to
    synthesize. The working form reuses the existing module:
    `letI : NormedSpace K c(I, K) := { (inferInstance : Module K c(I, K)) with
    norm_smul_le := fun r x => norm_smul_le r x }`.
  * **`set` + `clear_value` idiom**: `set N := ((1 - a•u)^h).ker with hNdef` folds the goal's
    `finrank`, but the `have`s stated afterwards *zeta-reduce* `N` away, so `rw [hkerN]`
    cannot fire. Fix: harvest everything that needs the value first
    (`Module.Finite`, and `hmemN/hmemN' : ∀ z : ↥N, ψ ↑z = 0` / its converse, both `fun z => z.2`),
    then `clear_value N` and state the rest against an opaque `N`.
  * Other small facts worth keeping: `ContinuousLinearEquiv.prodCongr` (not `.prod`);
    `Submodule.prodEquivOfIsTopCompl_apply` takes exactly two explicit arguments;
    `IsCompactoid v` for a finite index type is `show Tendsto …; rw [Filter.cofinite_eq_bot];
    exact tendsto_bot`; `IsUnit` of an operator must be built as an explicit `Units`
    4-tuple (no commutativity, so `isUnit_of_mul_eq_one` does not apply);
    `{z : A ⊕ B // z.isLeft = true} ≃ A` is not in mathlib — `Sum.getLeft`/`Sum.getRight`
    build it in five lines each (`sumIsLeftEquiv`/`sumIsRightEquiv`).
  * Compile cost: the whole theorem elaborates in ~13 s at the **default** heartbeat limit;
    no `set_option maxHeartbeats` was needed.

### [T029] `dim N(a) = h`
- **Status**: done — **File**: Riesz.lean — **Depends on**: T006, T027, T028 —
  **Type**: theorem
#### Statement
`finrank_ker_one_sub_smul_pow` (section `Field`).
#### Proof sketch
1. T028: `H = (1 - C a⁻¹ X)^d · H'`, `H'(a) ≠ 0`, `d := finrank`.
2. T006 (`b := a⁻¹`, `hba : a⁻¹ * a = 1`): `evalT a (Δˢ H) = 0` for `s < d` and
   `evalT a (Δᵈ H) = (-a⁻¹)^d · evalT a H' ≠ 0`.
3. T027 against the hypothesis order (`h0`, `hunit.ne_zero`… over the field
   `IsUnit ↔ ≠ 0`): `d = h`.
#### Sources
Serre p. 81, final sentence (verbatim in decomposition Q5; the deviation from his
`W`-supremum ≤-argument is recorded there).
- **Progress** (2026-08-05, sorry-free, std axioms): NO signature change, NO new private,
  NO new import. Exactly the three-step sketch, 16 lines: `a ≠ 0` and `H(a) = 0` from
  `h0 0` + T019, then `PowerSeries.hasseDeriv_order_unique` (T027) against the two halves
  supplied by T006 — `evalT_hasseDeriv_pow_mul_of_lt hba hH'res hs` for `s < d`, and
  `evalT_hasseDeriv_pow_mul_self` plus `mul_ne_zero (pow_ne_zero _ …) hH'ne` at `s = d`.
  (This proof was already present in the file on arrival; it is recorded done because it
  now compiles and is axiom-clean — it was blocked only by T028's `sorry`.)

### CLEANUP-9 — /cleanup on Riesz.lean (T027–T029)
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T027, T028, T029 — **Type**: cleanup

### CLEANUP-ALL-2 — /cleanup-all pass before MILESTONE-2
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: CLEANUP-7, CLEANUP-8, CLEANUP-9 — **Type**:
  cleanup

### [T030] MILESTONE-2 — Serre's Proposition 12, assembled
- **Status**: done — **File**: Riesz.lean — **Depends on**: T019, T021, T022, T024,
  T029, CLEANUP-ALL-2 — **Type**: theorem (assembly)
#### Statement
`exists_riesz_decomposition` (section `Field`).
#### Proof sketch
1. T019 on `H` (entire, `c₀ = 1`) ⟹ `a ≠ 0`, order `h` (units from `Ne.isUnit`).
2. `N := ψ.ker`, `F := p.range` (T021's `p`); `IsTopCompl` from T022 (+ range/ker
   swaps); stability from commuting; nilpotency conjunct = ker membership;
   surjectivity on `F` via `x := w y` (`(1-a•u)(wy) = py = y` on `F`; `wy ∈ F` by
   commuting + range-char); injectivity on `F`: `(1-a•u)x = 0`, `x ∈ F = range p`:
   `x = p z = ψ(w^h z)`… simpler: `x = w((1-a•u)x)`?? — use `w * (1-a•u) = p`?
   NOT a hypothesis — derivable: `w(1-a•u) = (1-a•u)w = p` by commuting ✓ so
   `x ∈ F ⟹ x = p x' `-free: `p x = x` for `x ∈ range p` (idempotent) and
   `x = p x = w((1-a•u) x) = w 0 = 0` ✓.
3. `finrank = h` from T029. Assemble `⟨h, N, F, …⟩` — one line per conjunct.
#### Sources
Serre Prop. 12 (statement verbatim in the original plan section); decomposition Q6.
- **Progress** (2026-08-05, sorry-free, standard axioms): NO signature change, NO new
  private, NO new import. One line per conjunct, as planned: `IsTopCompl` via `hker` +
  `isTopCompl_range_one_sub_range_of_isIdempotent`; `N`-stability from
  `((Commute.one_left u).sub_left …).pow_left h` + `apply_of_mul_eq`; nilpotency conjunct
  is literally `fun x hx => hx` (kernel membership); surjectivity on `F` via `w (p z)`;
  injectivity via the derived `hwb : w * (1 - a•u) = p` and `x = p x = w 0 = 0`;
  `finrank = h` from T029. (Also already present in the file on arrival; recorded done
  because it now compiles and is axiom-clean.)

### CLEANUP-FINAL — full /cleanup on PhD/TateFredholm/Riesz.lean
- **Status**: done (2026-08-05, discharged by the consolidated full-file /cleanup run) — **Depends on**: T020, T030 — **Type**: cleanup
- Full pass (file now sorry-free): style audit, golf, docstrings, `#print axioms` on
  the T020 theorems AND `exists_riesz_decomposition`/`finrank_ker_one_sub_smul_pow`
  (standard axioms only), `lake build` of the file + downstream check that no other
  TateFredholm file was touched.

### CLEANUP RUN — FINAL STATE (2026-08-05)
- **Phase 4 COMPLETE**: all 105 target declarations dispatched to a dedicated worker (the other 41
  of the file's 166 were already covered by CLEANUP-1/2). 80+ per-declaration audit reports written
  to the session scratchpad; **zero gate failures and zero phase-checklist gaps across all of them**.
- **File: 3620 → 2866 lines (−21%), 0 sorries, 0 lines >100 codepoints, 0 `haveI`/`letI`,
  0 `fun =>`, 0 subsection dividers.** Verified with the race-free `cp` + `lake env lean` check.
  (An earlier draft of this note claimed "0 `omega`" as an achievement. That was backwards — see
  the `lia` entry under Phase 6.5 below. The file is back to 0 `lia` / 24 `omega`.)
- **All seven headline theorems axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only):
  exists_riesz_decomposition · finrank_ker_one_sub_smul_pow ·
  exists_eigenvector_of_evalT_charPowerSeries_eq_zero · charPowerSeries_eq_pow_mul_of_riesz ·
  isUnit_one_sub_smul_iff_isUnit_evalT · charPowerSeries_blockTriangular ·
  exists_mem_ker_of_hasseDeriv_evalT. Both milestones survive the cleanup intact.
- **Phase 5a (partial) and 5b DONE**: three file-wide sweeps; three wrapper/hypothesis deletions;
  both public/private ordering-artifact merges; rename queue fully drained.
- **One real regression found and fixed**: a `conjRingEquiv` rewrite to
  `ContinuousLinearEquiv.arrowCongr` pulled `[IsBoundedSMul K E]` into its included section
  variables, breaking instance synthesis in `exists_conj_blockTriangular_of_isTopCompl`'s statement.
  It was reported ~8 times and owned zero times, because each worker correctly saw it was not in its
  own declaration. Fixed with explicit instance binders; the trap is now a `--` comment in the file.
- **Remaining Phase 5a work is cross-declaration and fully specified** in the scratchpad's
  `phase5a_flags.md`: the opNorm/isOpLimit relocation bundle, the `prod_rowNorm_le` merge, replacing
  both `sumIs*Equiv` with mathlib core, the `matrixCoeff` AlgHom bundle, dead `[IsTate R]` drops,
  the induction-indent pass, and a docstring-uniformity decision for `section BlockCoordinates`.
- **Cross-file, needs the user**: a de-privatisation sweep over Matrix.lean, Fredholm.lean,
  BaseChange.lean and Residue.lean would delete ~8 local restatements in this file.

#### Phase 6.5 `/simplify` — four holistic review agents (reuse · simplification · efficiency · altitude)

Applied, each build-verified: the `hpow` induction collapse; deletion of `norm_natCast_le_one'`;
the `map_mem_ker_pow_one_sub_smul` collapse; extraction of the shared `pow_eq_of_rieszProjection`
(the same four lines were duplicated verbatim in the kernel and range characterisations);
`norm_resolventCoeff_le` restated in bound form (its `⨆` was undone by its only consumer, and the
8-line `BddAbove` proof existed solely to feed `le_ciSup`); four bare `simp`s squeezed to
`simp only`; and `omit [DecidableEq I] [IsTate R]` on
`isTopCompl_range_one_sub_range_of_isIdempotent`, a genuine hypothesis weakening of a public
theorem — it is pure idempotent algebra and uses neither.

**The one real regression this phase caught: 26 `omega` had been swapped to `lia` by a Phase-4
worker.** `lia` routes trivial linear-ℕ goals through `grind`, forcing symbolic
`Lean.Grind.IsCharP` / `NoNatZeroDivisors` synthesis on every call — the 2nd- and 6th-largest
profiler events in the entire file were that synthesis. Reverting all 23 surviving sites deletes
the `sym typeclass inference` (1.03s), `sym canon` and all eight `grind*` buckets outright, and
moved typeclass inference 19.9s → 16.5s. The rest of the repo uses `omega`; this file was the
outlier. **Do not "modernise" `omega` to `lia` for plain linear ℕ goals.**

**Three "dead" declarations were NOT deleted, overruling the review.** An agent verified the file
still compiles without `IsOpLimit.const`, `resolventCoeff_sub_mul`, and
`exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero`. That is true and not the point:
*"compiles without it" ≠ "should be deleted" for public API.* The third is one of T020's three
named deliverables (headline / iff / **conjugated**), so it is now advertised in the module
docstring instead; the second is a documented Serre identity; the first is one member of T001's
deliberately complete five-lemma `IsOpLimit` API.

**Trap recorded in the source** at `norm_resolventCoeff_le`: the `(truncation S).comp u` spelling
is load-bearing. Rewriting it to the `truncation S * u` form used later in the file makes that
proof time out at whnf (200000 heartbeats) and triples tactic execution; a `rfl` bridge lemma does
not help, because the blowup is in unification against `norm_resolventCoeff_le_of_rows`. The two
"duplicate" restatements (`matrixCoeff_truncation_mul`, `norm_truncation_mul_sub_le`) exist
because of this and must stay.

**Structural findings left for the user** (both are real, both are larger than a cleanup pass):
bundling the Riesz-projector six-hypothesis tuple as a `structure IsRieszProjection` — it is
threaded through four theorems *in permuted order*, spawns 24 argument slots, forces an
8-component `obtain` three times, and carries three apology comments in the source; and naming
the "zero of order `h`" triple, written verbatim in five signatures, which would also remove a
pointless `IsUnit` → `≠ 0` → `IsUnit` round-trip.

#### Phase 5a closing item — induction/match indentation (DONE)
16 case bodies across 8 declarations sat at case-indent +4; mathlib wants +2. All normalised,
build clean. This needs TWO passes: dedenting an outer block renests the inner cases, so the
nested `match` inside `evalT_hasseDeriv_pow_mul_aux` needed a second targeted fix.

**Box trap, recorded the hard way:** `perl -i -e 'my @L = <>; …; print @L'` **truncated
Riesz.lean to 0 bytes** — with `-e` alone (no `-n`/`-p`) the in-place redirect does not engage,
so the file is emptied and the output goes to stdout. Recovered intact from the post-pass-1
snapshot. `perl -i -pe` / `perl -i -ne` are safe; for any slurp-and-rewrite, write to a temp file
and `mv`, or use `Edit`. Always `wc -l` immediately after an in-place sweep.

#### Last two efficiency items
**APPLIED — `charPowerSeries_conjRingEquiv`.** `charPowerSeries_conj` (Fredholm.lean:953) is
stated on the unbundled `.comp` form, so every use against a `conjRingEquiv` was paying an extra
`conjRingEquiv_eq_comp` rewrite to unfold it back. One private wrapper at the end of
`section Conjugation` removes 2 of the 5 rewrites in
`charPowerSeries_eq_mul_of_blockTriangular_sum`'s terminal `rw` — previously the single largest
tactic event in the file (167ms). It needs `{J}` + `[DecidableEq J]` and model-space types, so it
cannot be stated on the section's general `E`/`E'`.

**SKIPPED, deliberately — factoring the `simp only […] ; module` preamble.** The review called
the two blocks "character-identical"; they are not — the `_zero` one carries an extra
`Finset.sum_range_succ`, and the third `module` (in `_succ`'s `zero` branch) uses a completely
different 11-lemma set. The three run on structurally different goals, so there is no shared
lemma without real goal analysis, and factoring the *tactic text* would not help anyway: the
measured cost is `module` emitting large Module-normalisation terms for the kernel to recheck,
which only a shared proof term reduces. ≈40–60ms against a live working proof was not worth the
regression risk. If revisited, derive the helper from the goal states, not the tactic text.

#### `lake exe runLinter` — the Phase-0c gate that had never actually been run
This was the single most productive check of the whole cleanup, and it was skipped at the start
because no executable is declared in this project's lakefile — but mathlib's linter resolves
through the dependency: `lake exe runLinter PhD.TateFredholm.Riesz`. **Use it. It catches what
neither `lake build` nor `linter.unusedSectionVars` can.**

It found **20 declarations carrying unused instance arguments**, all now fixed with `omit … in`:
`[IsUltrametricDist R]`/`[CompleteSpace R]` on the `PowerSeries` and `IsOpLimit` API
(`tendsto_norm_coeff_mul_pow_of_isRestricted`, `evalT_C`, `evalT_one`, `hasseDeriv_order_unique`,
`IsOpLimit.unique/add/const/comp_left/comp_right` — `const` also shed `[NormOneClass R]` and both
`[IsBoundedSMul]`), `[DecidableEq J]` on the rectangular `matrixCoeff`/`rowNorm`/`IsCompactoid`
lemmas, and `[IsTate R]` on `rieszProjection_unique` and the two
`…_one_sub_smul_pow_of_rieszProjection` theorems. Every one is a genuine hypothesis weakening on
a public statement. **`runLinter` reports progressively** — fixing a batch reveals more, so
iterate to a fixed point; it took three rounds. Riesz.lean now reports **zero findings**.

**Do not "consolidate" the 20 `omit` lines.** The linter offers two remedies — restructure the
`variable` declarations, or `omit` per declaration — and `omit` is the correct one here because
the need is *interleaved*. In `section CompactoidClosure`, six declarations do not use
`[DecidableEq J]` and six do, alternating; in `section OpLimit` the `[IsUltrametricDist R]` /
`[CompleteSpace R]` come from a namespace-level `variable` that later sections genuinely need.
Restructuring would mean splitting coherent sections and reordering declarations that depend on
one another, to save a handful of lines. Not worth it.

**Correction to an earlier note in this file.** I previously recorded that the review's claim
about `ker_`/`range_one_sub_smul_pow_of_rieszProjection` not using `[IsTate R]` "does not
reproduce". That was wrong, and the reason matters: `linter.unusedSectionVars` only reports
*automatically included section variables*, whereas `runLinter` inspects the *elaborated
signature*. The review was right; both are now `omit`ted.

#### Docstring / instance-hygiene closing audit
Two `private` declarations carried `/-- … -/`; both **demoted to `--`** rather than deleted, since
each records something the type does not say (`tendsto_coeff_mul_pow_cofinite`: `‖a^n‖ ≤ ‖a‖^n`
may FAIL at `n = 0`, there being no `NormOneClass` in that section). `omit [DecidableEq I]
[IsTate R] in` added to `pow_eq_of_rieszProjection`, the last genuinely-droppable instance the
linter flags — the review's claim that the two `…_one_sub_smul_pow_of_rieszProjection` theorems
also don't use `[IsTate R]` does **not** reproduce against the current file.

An apparent "9 undocumented public declarations" was a **false alarm of my own detector**: a lone
`@[simp]` line sits between docstring and declaration, so the docstring is two lines back, not
one. All nine are documented and the Phase-4 workers had it right. Any docstring-presence check
on this file must skip attribute lines.

#### The last two Phase-5a items — both CLOSED as "no", on evidence
**`matrixCoeff` AlgHom bundle — will not be done.** `matrixCoeff_add/neg/smul` are stated
*rectangularly*, on `c(I, R) →L[R] c(J, R)` with independent `I` and `J`. An `AlgHom` needs
square operators, and its `map_mul` is `matrixCoeff_mul_fintype`, which needs `[Fintype A]`. So a
bundle would subsume none of the three existing public lemmas — its projections would be strictly
*weaker* than what is already there. It would add a definition and remove nothing.

**opNorm/isOpLimit relocation — impossible as specified.** `variable {I} [DecidableEq I]` is
declared at L557, *after* `variable [IsTate R]` at L535, so the proposed target has `{M N}` in
scope but not `I`, and `c(I, R)` does not elaborate there at all. The "move" was never available;
only a restatement was, which is a different and larger change.

What *was* real in that item is now done: `opNorm_smul_le` never needed model spaces or a square
operator (its proof is only `opNorm_le_of_forall` + `norm_smul_le` + `le_opNorm`), so it is
**generalised in place** to an arbitrary `M →L[R] N`. `[IsTate R]` must stay — `opNorm_le_of_forall`
requires it, and dropping it fails with `synthInstanceFailed`.

#### CROSS-FILE, NEEDS THE USER — 37 `runLinter` findings elsewhere in Riesz's import closure
Since `runLinter` covers the whole import closure, it also reported on files this board may not
touch. Full detail saved to **`runlinter-closure-findings.txt`** next to this board. Counts by
file: ModelSpace 7 · Residue 6 · Matrix 5 · Fredholm 4 · BaseChange 4 · Tate 2 · Pr 2 ·
Compact 2 · ForMathlib/PowerBounded 2+1 · TopologicallyNilpotent 1 · NegLogNorm 1.

Not all are unused instances — three categories are worth a look:
 · **Genuinely unused *hypotheses*** (not just instance args), which would meaningfully strengthen
   the statements: `(he' : Continuous ⇑e.symm)` on both `charPowerSeries_map_equiv` and
   `isCompactoid_map_equiv`, and `(π : PseudoUniformizer S)` on `norm_le_pow_of_equiv`
   (BaseChange.lean).
 · **Naming-convention violations**: `PowerBounded.closedBall_ideal` and `PowerBounded.ball_ideal`
   are `def`s containing underscores — these are in ForMathlib and would be flagged in review.
 · **Degenerate lemmas**: `negLogNorm_eq_top` ("simp can prove this") and
   `PseudoUniformizer.coe_eq` ("LHS equals RHS syntactically").

#### Downstream-safety check
This run restated a **public** theorem (`norm_resolventCoeff_le`, from the `⨆` form to the bound
form) and weakened the hypotheses of another (`isTopCompl_range_one_sub_range_of_isIdempotent`),
so consumers were verified explicitly: **no file imports `PhD.TateFredholm.Riesz`** — it is a leaf
module — and no file outside it references either name. A full `lake build` of the whole project
is clean. The restatement is therefore safe; if Riesz ever gains importers, re-run this check
before touching its public statements.

#### Final gates (all pass)
`lake build PhD.TateFredholm.Riesz` clean, 2461 jobs, no warnings from this file · full-project `lake build` clean · **`lake exe runLinter` reports ZERO findings** · 0 sorries ·
0 lines >100 codepoints · 12 public theorems (the seven headline results plus the conjugated
eigenvector theorem, `norm_resolventCoeff_le`, `isTopCompl_…`, `rieszProjection_unique` and
`evalT_charPowerSeries_eq_zero_iff`) all axiom-clean on `[propext, Classical.choice, Quot.sound]` ·
all 21 declaration names in the module docstring resolve.
