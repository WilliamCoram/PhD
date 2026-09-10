# Ticket Board — Jacobs Ch. 2 (Tranche A: slopes of `M₂,₂`)

**BOARD PATH: `.mathlib-quality/jacobs/`** (NOT the default board, NOT qmf).  Workers:
tell every `/beastmode` invocation this path.  Skeleton is canonical: every ticket =
"fill the named `sorry`s in the named file"; statements are already stated and
`lake build PhD.Jacobs.Slopes` is green.  Read `decomposition.md` (same directory) for
source quotes, entry-valuation tables, and the three thesis errata before starting any
U3Data/Slopes ticket.

## Summary — **BOARD COMPLETE (2026-08-05)**
- All 21 proof tickets + all cleanup tickets DONE.  Final gates: `lake build
  PhD.Jacobs.Slopes` green (2317 jobs), 0 sorries in all five files, 0 warnings,
  milestone axioms exactly [propext, Classical.choice, Quot.sound] (independently
  re-verified after cleanup).  Cleanups ran as ONE consolidated post-milestone wave
  (deviation from the interleaved cadence, recorded: proof wave was worker-parallel, so
  cleanup was deferred to avoid churn under active importers; 21→0 warnings, docstrings
  added to 38 public decls, 2 dead `classical` + 1 unused import + scratch comments
  removed, NO renames/statement changes).
- OPEN FOLLOW-ON TRANCHES (no tickets here; see decomposition.md AGs + user-flagged
  notes): AG-B (identification: the definitions ARE U₃'s matrix — blocked on QMF
  T016/T017), AG-NP (val points → Newton-polygon slopes 1/2, 3/2, …), AG-W (eigenblock
  splitting), AG-EXT (§2.2: M₃,₃, λ ∈ {1,2}).
- Historical summary line (planning-time): 21 proof/def tickets + 11 cleanup tickets.
- Milestone: J021 (`sq_norm_charCoeff_M22op` / `val_charCoeff_M22op` = [Jac Cor 2.16])
- Parallel capacity at start: J001, J005, J009, J010, J016 (5 workers)
- Deferred tranches (NO tickets here): AG-NP, AG-W, AG-EXT, AG-B — see decomposition.md.
  **AG-B is blocked on the QMF board's T016/T017 port infrastructure — check
  `.mathlib-quality/qmf/tickets.md` before opening it.**

## ⚠ API CHANGE (2026-08-04, user-approved, applied while AG-W Wave 1 was paused)

The `(ϖ : PseudoUniformizer K) (hϖ : (ϖ : K) = 3)` argument pair has been **removed from
every statement**.  The normalisation is now a definition, `Jacobs.ϖ₃` in
`PhD/Jacobs/SlopeTheorem.lean`:

- `Jacobs.ϖ₃ (h3 : ‖(3 : K)‖ < 1) : PseudoUniformizer K` (needs `[CharZero K]`), built via the
  new `PseudoUniformizer.ofNormLtOne` in `PhD/TateFredholm/Tate.lean`; `@[simp] coe_ϖ₃`
  gives `((ϖ₃ h3 : PseudoUniformizer K) : K) = 3` by `rfl`.
- The valuation is spelled **`(ϖ₃ h3).val`**, no longer `ϖ.val`.
- New call shapes: `val_charCoeff_of_unit_minors h3 u hdiv hmin m`;
  `val_charCoeff_M22op ω h3 ht hν2 hνc hω m`; likewise the four `SlopeReading` theorems
  (`isNewtonPolygonOf_val_charCoeff`, `unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries`,
  `isNewtonPolygonOf_val_charCoeff_M22op`, `unitSlope_newtonPolygon₀OfPowerSeries_M22op`).
- `SlopeReading`'s case-A section gained `[CharZero K]` (case B and `Slopes`/`U3Data`/
  `DiamondW` already had it).  Rationale: `h3` alone does not give `(3 : K) ≠ 0` — a
  char-3 field has `‖3‖ = 0 < 1`.

**NOT changed**: the `_`-named explicit-hypothesis convention for AG-W defs (`epsOp*`,
`delta*`, `M11op`/`M33op`, `Bop`/`Binvop`) recorded in `decomposition.md` — `h3`-as-def-argument
stays exactly as it is.  No `BlockOp.lean` / `DiamondW.lean` declaration referenced `ϖ`, so no
AG-W proof breaks; `lake build PhD.Jacobs.SlopeReading` green (2331 jobs).

---

### [J001] Residue-characteristic norm lemmas
- **Status**: done (2026-08-03; coprime case via Bézout `Nat.gcd_eq_gcd_ab` + `IsUltrametricDist.norm_add_le_max`/`norm_natCast_le_one`/`norm_intCast_le_one` [all take R explicit]; valuation case via `Nat.ordProj_mul_ordCompl_eq_self` + `push_cast` + `Nat.coprime_ordCompl` [takes `Nat.Prime`, NOT `Prime` — no `.prime`] + `Nat.factorization_def`; factorial via `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (root ns, needs `Fact (Nat.Prime 3)` haveI) + `pow_le_pow_of_le_one` + omega; build clean) | **File**: PhD/Jacobs/PadicAnalytic.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Decls**: `norm_natCast_eq_one_of_coprime`, `norm_natCast_eq_pow_padicValNat`, `sq_norm_factorial_ge`
- **Sketch**: (1) `‖(n:K)‖ ≤ 1` from ultrametricity (search `IsUltrametricDist` +
  `norm_natCast` via loogle; exists as `IsUltrametricDist.norm_natCast_le_one` or
  nearby).  (2) Coprime case: Bézout `a·n + b·3 = 1` in ℤ, push to K:
  `1 = ‖a·n + b·3‖ ≤ max(‖n‖, ‖3‖)`; since `‖3‖ < 1`, `‖n‖ = 1` (careful with ℤ-casts;
  `Int.emod`-free route: `Nat.Coprime` gives `n.gcd 3 = 1`, use `Nat.gcd_eq_gcd_ab`).
  (3) Factor `n = 3^v · m` with `m` coprime (`padicValNat` + `Nat.ord_proj/ord_compl`),
  multiplicativity of the field norm.  (4) Factorial: `padicValNat 3 (n!)` via mathlib
  Legendre (`Nat.Prime.factorial` family — search `padicValNat factorial`); bound
  `2·v₃(n!) ≤ n − 1` for `n ≥ 1` (digit-sum form `sub_one_mul_padicValNat_factorial`),
  then square `norm_natCast_eq_pow_padicValNat`.
- **Mathlib**: `padicValNat`, `Nat.gcd_eq_gcd_ab`, `Nat.ord_proj_mul_ord_compl_eq_self`,
  `sub_one_mul_padicValNat_factorial` (verify names by loogle at pickup).
- **Sources**: standard; consumed by [Jac p. 29, 38] steps.  **Generality**: any
  ultrametric `NontriviallyNormedField` + `CharZero`; prime hardcoded to 3 (see plan).

### [J002] Log/exp: convergence and norm bounds
- **Status**: done (2026-08-03, worker; all 4 proved; PUBLIC reusable helpers added: `summable_padicLog_term` (CLOSED disc ‖u-1‖²≤‖3‖ — covers both later use-cases), `norm_padicExp_term_le`, `summable_padicExp_term`; private NatAux section (two_mul_le_three_pow, padicValNat_three_succ_le via padicValNat_le_nat_log + Nat.log_lt_self, etc.) + norm_three_pos; KEY: `IsUltrametricDist.norm_tsum_le_of_forall_le` needs NO Summable hyp; mathlib has `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` (own version of TateFredholm's) via the IsUltrametricDist.nonarchimedeanAddGroup instance — file stays mathlib-only-imports (added Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean); `Summable.tsum_eq_zero_add` peels n=0; axioms standard; verified 0 errors) | **File**: PhD/Jacobs/PadicAnalytic.lean | **Depends**: J001 | **Type**: lemma
- **Decls**: `padicLog_one`, `padicExp_zero`, `norm_padicLog_le`, `norm_padicExp_sub_one_le`
- **Sketch**: simp lemmas: `tsum` of eventually-0/geometric-at-1 terms (`tsum_eq_single 0`
  for exp at 0 after `pow_zero`; log at 1: all terms 0).  Bounds: termwise
  `‖(u−1)^{n+1}/(n+1)‖ ≤ ‖3‖^{n+1}·‖3‖^{−v₃(n+1)}` and `v₃(n+1) ≤ log₃(n+1) ≤ n` gives
  `≤ ‖3‖` for every term (induction-free: `3^{v₃ m} ≤ m ≤ 3^n·…`; cleanest:
  `v₃(n+1) ≤ n` since `3^{v₃(n+1)} ∣ n+1 ≤ 3^n`… prove `padicValNat 3 m < m` via
  `Nat.pow_lt_pow` chain, or `Nat.padicValNat_lt_self`-type search).  Then
  `norm_tsum_le_iSup` (TateFredholm.Tate) + summability from term → 0.  Exp: split
  head `n = 0,1`; tail terms `‖w‖^n/‖n!‖`: squared bound
  `‖w‖^{2n}·‖3‖^{−(n−1)} < ‖3‖^{n}·‖3‖^{−(n−1)}·‖w‖^{…}` — follow the `v`-arithmetic
  `n·v(w) − (n−1)/2 > v(w)` for `n ≥ 2` ⇔ `(n−1)(v(w) − 1/2) > 0` ✓ (work squared
  throughout to stay in `npow`).
- **Mathlib**: `tsum_eq_single`, `Summable.tsum_eq_add_tsum_ite` or
  `tsum_eq_add_tsum_ite`, TateFredholm `summable_of_tendsto_cofinite`,
  `norm_tsum_le_iSup`.
- **Sources**: [Kob84 Ch. IV §1]; [Jac p. 38].  **Generality**: as J001.

### [J003] Exp additivity, exp∘log, log of products
- **Status**: done (2026-08-03, worker; ALL THREE proved, axiom-clean, NO reduced-scope exit needed. ROUTE DEVIATION (recorded): instead of [Kob84 IV.2]'s double-series rearrangement, the keystone went through **Iwasawa's limit formula** `tendsto_padicLog : (u^(3^k) − 1)/3^k → padicLog u` (binomial expansion + `Nat.add_one_mul_choose_eq` + ultrametric dominated convergence — new private helper `tendsto_tsum_of_forall_norm_le`); then `norm_padicLog_eq : ‖padicLog u‖ = ‖u−1‖` EXACTLY, `eq_of_padicLog_eq` (injectivity), `padicLog_padicExp`, and the two targets as corollaries — no rearrangement, no rational-coefficient identity, no PowerSeries.subst. 13 new helpers incl. public `norm_eq_one_of_norm_sub_one_lt_one`, `summable_norm_padicExp_term`, `norm_padicExp_sub_one_sub_self` (quadratic error), `norm_pow_three_pow_sub_one`, `padicExp_pow_three_pow`. Cauchy product for padicExp_add via `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` + `Commute.add_pow'`; geometric-mean trick r := (1+q)/2 avoids Real.sqrt. RENAMES: `Nat.add_one_mul_choose_eq`, `tendsto_finsetProd`, `mul_lt_mul_of_pos_left`. IMPORTS ADDED (mathlib-only): BigOperators.Field, Normed.Ring.InfiniteSum, Nat.Choose.Sum, Nat.Factorial.BigOperators; NB `linear_combination` NOT in this import set. PERF TRAP: `(summable_nat_add_iff 1).2` needs explicit (f := …) else heartbeat blowup. Verified: 0 errors, 5 sorries remain = exactly J004) | **File**: PhD/Jacobs/PadicAnalytic.lean | **Depends**: J002 | **Type**: theorem (analytic core, LARGE)
- **Decls**: `padicExp_add`, `padicExp_padicLog`, `padicLog_mul`
- **Sketch**: (1) `padicExp_add`: Cauchy product of the two absolutely-summable series
  (ultrametric ⇒ summable ⇒ multipliable rearrangement): mathlib
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` (or `_of_summable_norm` variant) +
  binomial `(a+b)^n = ∑ choose`; the `1/n!`-bookkeeping via `Nat.add_choose_le`-style
  identities (`n!·(choose n k) = …`).  (2) `padicExp_padicLog`: the formal identity
  `exp(log(1+x)) = 1+x` at the level of double series: expand, reorder (absolute
  summability on the disc `‖u−1‖² < ‖3‖`), and use the ℚ-coefficient identity — realise
  via mathlib's FORMAL `PowerSeries.exp`/`PowerSeries.log` composition identity if
  present (search `PowerSeries.exp_log`/`log_exp`; if absent, prove the coefficient
  identity over ℚ by `PowerSeries` algebra and transport along evaluation — the
  standard route, [Kob84 IV.2]).  Fallback decomposition if the double-series reorder
  fights: prove exp injective-on-disc via `‖exp a − exp b‖ = ‖a − b‖` (from J002's
  dominant-linear-term bound applied to `exp(a) − exp(b) = exp(b)(exp(a−b) − 1)`), then
  derive (3) from (1)+(2) and (2) from … NO: (2) is primitive; keep order (1),(2),(3).
  (3) `padicLog_mul`: `exp(log u + log v) = uv = exp(log(uv))` by (1),(2); conclude by
  exp-injectivity on the disc (isometry consequence of J002 as above).
- **Mathlib** (VERIFIED 2026-08-03, exact signatures): Cauchy product =
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : ℕ → R}`
  + `summable_mul_of_summable_norm` + `summable_norm_sum_mul_antidiagonal_of_summable_norm`,
  all in `Mathlib/Analysis/Normed/Ring/InfiniteSum.lean:45-123` (root namespace; the
  `Finset.antidiagonal n` inner sum is exactly the binomial-pairing shape).  Formal side:
  `PowerSeries.exp`/`log` EXIST (`RingTheory/PowerSeries/{Exp,Log}.lean`) with
  `exp_mul_exp_eq_exp_add`, `coeff_exp = 1/n!`, `coeff_log`, `logOf f = (log A).subst (f-1)`,
  `HasSubst.log`, `HasSubst.exp_sub_one`, `logOf_one_add_X`, `deriv_log`, and
  `exp_unique_of_derivative_eq_self` — NO ready `exp∘log = id` identity, but it is
  derivable formally via the derivative-uniqueness lemma (g := exp.subst (logOf f) has
  g' /g = (logOf f)' pattern) or via the ℚ-coefficient transport route in the sketch.
  `add_pow`, `Nat.choose` as sketched.
- **Sources**: [Kob84 Ch. IV §2] (the thesis's cited reference for these facts).
- **Generality**: as J001.  **Sizing**: source ≈ 2 pages ⇒ largest PadicAnalytic ticket.

### [CLEANUP-J1] /cleanup PhD/Jacobs/PadicAnalytic.lean (mid-file cadence)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J003 | **Type**: cleanup (board `.mathlib-quality/jacobs/`)

### [J004] unitPow and binomial-series bounds
- **Status**: done (2026-08-04, worker; all five proved via scratch-file validation then port (good pattern: zero churn on the file while a sibling built against it); no new helpers/imports; unitPow_mul via disc-upgrade nlinarith + padicLog_mul + padicExp_add with a reusable local hbound; binomial bound: Finset.prod_range_succ' peel + norm_prod/prod_le_one tail + sq_norm_factorial_ge through div_le_div_of_nonneg_left + field_simp;ring. Axioms: standard three on all five; TRANSITIVE CHECK CONFIRMED: norm_coeff_h02_le/h12_le now sorryAx-FREE. PadicAnalytic.lean COMPLETE (0 sorries) — the R1 API gap is closed. New unusedSectionVars warning on binomialCoeff_zero (pre-existing pattern) → CLEANUP-J1/J2 punch-list) | **File**: PhD/Jacobs/PadicAnalytic.lean | **Depends**: J003, CLEANUP-J1 | **Type**: lemma
- **Decls**: `unitPow_one`, `unitPow_mul`, `norm_unitPow_sub_one_le`, `binomialCoeff_zero`, `sq_norm_binomialCoeff_mul_pow_le`
- **Sketch**: `unitPow_one`: `padicLog_one` + `mul_zero` + `padicExp_zero`.
  `unitPow_mul`: J003(3) + J003(1) after disc-membership checks
  (`‖t·log u‖² ≤ ‖t‖²‖3‖² < ‖3‖` via J002 bound).  `norm_unitPow_sub_one_le`: J002 exp
  bound at `w = t·log u` + `norm_padicLog_le`.  Binomial: `binomialCoeff_zero` by
  `simp [binomialCoeff]`.  Tail bound: `‖∏_{k<n}(t−k)‖ ≤ ‖t‖·1` (first factor `t`,
  rest integral: `‖t−k‖ ≤ max(‖t‖,‖k‖) ≤ 1`), so squared:
  `‖bc·eⁿ‖² ≤ ‖t‖²·‖3‖^{n−1}⁻¹-inverse-of-factorial (J001 `sq_norm_factorial_ge`)
  ·‖3‖^{n}` (from `he` squared, `‖e‖^{2n} ≤ ‖3‖^n`) `= ‖t‖²‖3‖^{n−(n−1)} = ‖t‖²‖3‖` ✓
  (mind: division by `n!` means MULTIPLYING the bound by `‖n!‖⁻²` and using
  `sq_norm_factorial_ge` as a LOWER bound on `‖n!‖²` — direction check!).
- **Mathlib**: `Finset.prod_range_succ'` (peel `k = 0`), `norm_prod_le`-style
  (multiplicative norm: `norm_prod` exact for fields).
- **Sources**: [Jac p. 29] (both displays quoted in decomposition.md R1).
- **Generality**: as J001.

### [CLEANUP-J2] /cleanup PhD/Jacobs/PadicAnalytic.lean (final)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J004 | **Type**: cleanup

### [J005] `idx` multidegree API
- **Status**: done (2026-08-03; simp [idx, Finsupp.single_apply] closes both apply lemmas; injectivity via congrArg at 0/1 + Prod.ext; first-compile) | **File**: PhD/Jacobs/GenFun.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Decls**: `idx_apply_zero`, `idx_apply_one`, `idx_injective`
- **Sketch**: `simp [idx, Finsupp.single_apply, Finsupp.add_apply]` (0 ≠ 1 in Fin 2 via
  `decide`/`Fin.ext_iff`).  Injectivity: from the two application lemmas
  (`fun h => Prod.ext (by simpa using congrArg (· 0) h) …`).
- **Mathlib**: `Finsupp.single_apply`, `Finsupp.add_apply`.  **Sources**: none (device).
- **Generality**: n/a.

### [J006] The operator-from-matrix construction
- **Status**: done (2026-08-03, worker, first-compile; ofCoeffs = LinearMap.mkContinuous over private ofCoeffsFun/ofCoeffsLinear; CONVENTION CONFIRMED: matrixCoeff u j i = u (single i 1) j, j = row/output ✓ matches board; vanishing-at-∞ needed NO tsum splitting — split the SUP over i∈S vs ∉S (Filter.eventually_all_finset, explicit Finset arg); public `ofCoeffs_apply … := rfl` ADDED for J008/J015 use; deprecations: use NormedAddGroup.tendsto_nhds_zero, div_le_iff₀, pow_le_one₀; axioms standard; 5 J008 sorries remain) | **File**: PhD/Jacobs/GenFun.lean | **Depends**: J005 | **Type**: def+lemma (core infrastructure)
- **Decls**: `ofCoeffs`, `matrixCoeff_ofCoeffs`, `hyps_of_row_decay`
- **Sketch**: **First re-verify the row/column convention against
  `TateFredholm/Matrix.lean:34` (`matrixCoeff u j i`) — see plan.md "hazards".**
  Construction: for `f : c(ℕ,K)`, define `g j := ∑'_i, M j i * f i` (summable:
  `‖M j i·f i‖ ≤ C·‖f i‖ → 0` cofinitely + `summable_of_tendsto_cofinite`
  [TateFredholm.Tate]); `g ∈ c(ℕ,K)`: `‖g j‖ ≤ sup_i ‖M j i‖·‖f‖` via
  `norm_tsum_le_iSup`, and `g j → 0` from column decay + a dominated/`ε`-argument:
  fix `ε`; `‖f‖-scaled`: split `f` by a finite truncation `S` with `‖f∖S‖ < ε/C`
  (cSpace API `tendsto_cofinite`), then `g j = ∑_{i∈S} + tail`, first part → 0 by
  finitely many column decays, tail ≤ C·ε… (this is [Ser62 Prop. 3]'s standard
  argument).  Linearity: `tsum_add`, `tsum_mul_left`.  Continuity: the uniform bound
  `‖g‖ ≤ C‖f‖` ⇒ `LinearMap.mkContinuous`.  Spec: `matrixCoeff (ofCoeffs M) j i`:
  unfold `matrixCoeff` (it evaluates at `cSpace.single i 1`), `tsum_eq_single i`.
  `hyps_of_row_decay`: `C := ‖c‖` (`pow_le_one` on `‖q‖`), decay:
  `squeeze_zero_norm` against `‖c‖‖q‖^j → 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`
  composed to cofinite = atTop on ℕ).
- **Mathlib**: `LinearMap.mkContinuous`, `tsum_eq_single`, `tsum_add`, `tsum_mul_left`,
  `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Nat.cofinite_eq_atTop`; TateFredholm
  `cSpace.single`, `cSpace.tendsto_cofinite`, `norm_tsum_le_iSup`,
  `summable_of_tendsto_cofinite`.
- **Sources**: [Ser62 Prop. 3] = [Jac Prop. 1.7 p. 9] ("The map which associates an
  element u ∈ L(E,F) to the sequence (u(eᵢ)) is an isomorphism …").
- **Generality**: any `(K)` as in plan; index ℕ (project-local; `I`-generic later if
  AG-W needs `ℕ × Fin 3`).

### [J007] diagRescale coefficient calculus
- **Status**: done (2026-08-03; coeff_diagRescale = rfl [MvPowerSeries function-type defeq]; rest by ext p + simp only [coeff_diagRescale, mul_pow/map_add] + ring; first-compile) | **File**: PhD/Jacobs/GenFun.lean | **Depends**: J005 | **Parallel**: yes (with J006) | **Type**: lemma
- **Decls**: `coeff_diagRescale`, `diagRescale_diagRescale`, `diagRescale_one_one`, `diagRescale_add`
- **Sketch**: all four are coefficientwise: `MvPowerSeries` ext (`funext p` — the type
  IS a function type; or `MvPowerSeries.ext` + `coeff`), then `ring`/`mul_pow` −
  `one_pow`, `mul_add`.  `coeff_diagRescale` is `rfl`.
- **Mathlib**: `MvPowerSeries.ext`, `map_add` (coeff linear).  **Sources**:
  [Jac §1.1 Prop. 1.3] (quoted in decomposition.md R2).  **Generality**: total in α, β
  (thesis excludes 0; our statements hold totally — recorded).

### [CLEANUP-J3] /cleanup PhD/Jacobs/GenFun.lean (cadence after 3rd file ticket)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J007, J006 | **Type**: cleanup

### [J008] Diagonal operators, Prop 1.3, compactoid criterion
- **Status**: done (2026-08-03; file at 0 sorries, independently verified `lake build PhD.Jacobs.GenFun` 0 errors / 0 sorry-warnings by orchestrator; worker report landed: all 6 decls proved, axioms standard [propext, Classical.choice, Quot.sound]; PUBLIC helper `Jacobs.diagOp_apply (a) (ha) (f) (j) : diagOp a ha f j = a j * f j` ADDED (J020 will want it); `cSpace.single_apply_of_ne` hypothesis direction is `j ≠ i` (applied ≠ support); defeq facts: smul on c(ℕ,K) is pointwise (ModelSpace.lean:84) and `matrixCoeff u j i ≡ u (single i 1) j` — plain `show` crosses both, no transport needed; `matrixCoeff_diagOp` closes by matrixCoeff_ofCoeffs because diagOp is DEFINITIONALLY that ofCoeffs; IsCompactoid/rowNorm unfold definitionally. Punch-list for CLEANUP-J3/J4: pre-existing linter.unusedSectionVars on hyps_of_row_decay/coeff_diagRescale/diagRescale_* . GenFun.lean COMPLETE: full §1.1 layer proved) | **File**: PhD/Jacobs/GenFun.lean | **Depends**: J006, CLEANUP-J3 | **Type**: lemma
- **Decls**: `isCompactoid_of_row_decay`, `matrixCoeff_ofGenFun`, `diagOp`, `matrixCoeff_diagOp`, `matrixCoeff_diagOp_comp`
- **Sketch**: `diagOp a ha := ofCoeffs (fun j i => if j = i then a j else 0) ⟨1, …⟩ …`
  (column decay: eventually-0).  `matrixCoeff_diagOp` from `matrixCoeff_ofCoeffs`.
  Composition: `matrixCoeff` of a composite: `matrixCoeff (u∘v) j i =
  ∑'_k matrixCoeff u j k · matrixCoeff v k i` — prove the needed special case directly:
  `(diagOp a)∘u∘(diagOp b)` applied to `single i 1`: `diagOp b (single i 1) = b i •
  single i 1` (tsum_eq_single), then `u`, then `diagOp a` reads row j.
  `isCompactoid_of_row_decay`: `rowNorm u j = ⨆ i, ‖matrixCoeff u j i‖ ≤ ‖c‖‖q‖^j`
  (`Real.iSup_le`), `IsCompactoid` = `Tendsto rowNorm cofinite (𝓝 0)` (check exact
  def at `Matrix.lean:376`), squeeze.
- **Mathlib**: `Real.iSup_le`, `squeeze_zero_norm`.  **Sources**: [Jac Cor 1.10,
  Prop 1.3] (quotes in decomposition.md R2).  **Generality**: decay rate `‖q‖ < 1`
  generalises the thesis's `1/3`.

### [CLEANUP-J4] /cleanup PhD/Jacobs/GenFun.lean (final)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J008 | **Type**: cleanup

### [J009] Determinant valuation lemmas
- **Status**: done (2026-08-03, worker; det bound via Matrix.det_apply + IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg + Int.units_eq_one_or for sign + Equiv.prod_comp; det_row_smul_pow = Matrix.det_mul_column [CONFIRMED: det_mul_column scales FIRST index — names are opposite of wording] + Finset.prod_pow_eq_pow_sum; Finset lemma via new private helper `sum_range_le_sum_and_eq` (induction on m, max'-extraction kept opaque to dodge motive issues; NB `Finset.range_add_one` is the current name, range_succ is GONE); verified: 0 errors, axioms standard) | **File**: PhD/Jacobs/SlopeTheorem.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Decls**: `norm_det_le_of_row_bound`, `det_row_smul_pow`, `choose_two_lt_sum_of_ne_range`
- **Sketch**: (1) Leibniz `Matrix.det_apply`: each term
  `‖sgn·∏ A (σ j) j‖ = ∏ ‖A (σ j) j‖ ≤ ∏ ‖3‖^{w (σ j)} = ‖3‖^{∑ w}` (reindex by σ);
  finite ultrametric sum bound (`IsUltrametricDist.norm_sum_le_of_forall_le` — verify
  name).  (2) `det_row_smul_pow`: this is det of `diag(3^j) * B`:
  `Matrix.det_mul`, `Matrix.det_diagonal`, `Finset.prod_pow_eq_pow_sum`.  (3) Finset:
  strong induction on `m` or direct: let `S ≠ range m`, `|S| = m`; then some `s ∈ S`,
  `s ≥ m` (else `S ⊆ range m` with equal cards ⇒ equal); `∑_{S} ≥ s + ∑_{S∖{s}} ≥
  m + (m−1)(m−2)/2`… careful — cleanest: `∑_{i∈S} i ≥ ∑_{i∈range m} i` for ANY
  m-subset (exchange/`Finset.sum_range_id_le_sum_of_card_le`-search; if absent, induct:
  min element ≥ 0, strip), with equality iff `S = range m`.  Then `+1` from strictness
  in ℕ.  (`Finset.range_id_eq_sum`? loogle `Finset.sum_range_id`.)
- **Mathlib**: `Matrix.det_apply`, `Matrix.det_mul_column` (verified: first-index
  scaling, Determinant/Basic.lean:306), `Equiv.Perm.sign`, `Finset.prod_pow_eq_pow_sum`,
  `Finset.sum_range_id_mul_two`; ultrametric finite-sum bound = 
  `IsUltrametricDist.exists_norm_finsetSum_le` (∃-witness form, Normed/Group/Ultra.lean
  — verified 2026-08-03; bound each witness term).
- **Sources**: [Jac proof of Thm 2.12 pp. 34–35] (quoted, decomposition.md R3).
- **Generality**: (1),(2) any ultrametric normed field; (3) pure ℕ.

### [J010] Dominant-term tsum + charCoeff scaling
- **Status**: done (2026-08-03, worker; KEY DISCOVERY: `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg` needs NO summability hypothesis — reuse everywhere downstream; `Summable.tsum_eq_add_tsum_ite` is protected; degenerate c<0/singleton-ι branch genuinely needs a `by_cases ∀ i, i = i₀` split; charCoeff_smul: matrixCoeff of smul is RFL through the cSpace/Ix synonyms, then Matrix.det_smul + Fintype.card_coe + tsum_mul_left; verified: 0 errors, axioms standard. 3 unusedSectionVars linter warnings deferred to CLEANUP-J5 [TateFredholm precedent: file-scope set_option]) | **File**: PhD/Jacobs/SlopeTheorem.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Decls**: `norm_tsum_eq_of_dominant`, `charCoeff_smul`
- **Sketch**: (1) `tsum f = f i₀ + ∑' i ≠ i₀` (`tsum_eq_add_tsum_ite`/`Summable.tsum_ite_sub`
  route); tail norm ≤ c by `norm_tsum_le_iSup` (TateFredholm) over the ≠-subtype;
  ultrametric `‖a + b‖ = ‖a‖` when `‖b‖ < ‖a‖` (`norm_add_eq_left`-search /
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne`).  (2) `charCoeff (λ•u) n`: unfold
  (`Fredholm.lean:155`): minors of `λ•u`: `matrixCoeff (λ•u) = λ·matrixCoeff u`
  (linearity of evaluation — small lemma), `Matrix.det_smul` gives `λ^{|S|}`, pull out
  of the tsum (`tsum_mul_left`), `|S| = n` on the summation set.
- **Mathlib**: `tsum_mul_left`, `Matrix.det_smul`, `tsum_eq_add_tsum_ite`.
- **Sources**: [Jac pp. 35–36] (the `1/(ω(2ω+1))`-scalar step of Cor 2.16).
- **Generality**: `norm_tsum_eq_of_dominant` is mathlib-PR-shaped; keep clean.

### [J011] **Theorem 2.12** (abstract slope theorem)
- **Status**: done (2026-08-03; SlopeTheorem.lean at 0 sorries — BOTH `norm_charCoeff_of_unit_minors` and `val_charCoeff_of_unit_minors` proved; independently verified `lake build` 0 errors / 0 sorry-warnings by orchestrator; worker report landed: axioms standard, no sorryAx; 5 private helpers: `finEquivRange m : Fin m ≃ ↥(range m)` (explicit equiv, both inverses rfl — orderIsoOfFin avoided), `three_ne_zero_of_unit_minors` (from hmin 2 via det_eq_zero_of_row_eq_zero — the char-3 degeneracy trick worked), `isCompactoid_of_norm_matrixCoeff_le`, `norm_minor_le_pow_sum`, `norm_minor_range`. NAME DISCOVERIES: `pow_lt_pow_right_of_lt_one₀` (the ₀-suffixed one; unsuffixed does NOT exist); `Matrix.det_submatrix_equiv_self e A : det (A.submatrix e e) = det A` with ↥S-Matrix.of vs Fin-m-Matrix.of DEFEQ (no submatrix plumbing); `Equiv.sum_comp` + `Finset.sum_coe_sort` for index-sum transport; `Fin.sum_univ_eq_sum_range` + `Finset.sum_range_id` + `Nat.choose_two_right`; val bridge = val_of_ne_zero + Real.log_pow + div_self (log ≠ 0 from `(ϖ₃ h3).log_norm_neg.ne`, spelling updated by the `ϖ₃` refactor — see the API CHANGE banner at the top of this board) — single rw chain, NO WithTop plumbing. THE FILE IS COMPLETE: the [Jac Thm 2.12] layer is done) | **File**: PhD/Jacobs/SlopeTheorem.lean | **Type**: theorem (core)
- **Decls**: `norm_charCoeff_of_unit_minors`, `val_charCoeff_of_unit_minors`
- **Sketch**: `charCoeff u m = (−1)^m ∑'_{S : Finset ℕ, |S|=m-filtered} det(minor u S)`
  (read the exact `TateFredholm.charCoeff`/`minor` shape first — `Fredholm.lean:33,155`;
  the tsum runs over `{S : Finset ℕ // S.card = m}` or via an indicator — adapt).
  Dominant index `S_m = Finset.range m`: `‖det minor S_m‖ = ‖3‖^{C(m,2)}` via J009(2)
  factorisation `minor entries = 3^j · N`-form + `hmin m` (norm-mult:
  `‖3^{∑} · det N‖ = ‖3‖^{m(m−1)/2}·1`; `∑_{j<m} j = C(m,2)` by
  `Finset.sum_range_id`… = `Gauss`).  Other S: J009(1) with `w j = j` +
  J009(3): `‖det minor S‖ ≤ ‖3‖^{∑_{j∈S} j} ≤ ‖3‖^{C(m,2)+1} < ‖3‖^{C(m,2)}` (strict:
  `pow_lt_pow_right_of_lt_one`, needs `h3` and `‖3‖ > 0`).  Conclude with J010(1)
  (summability from `TateFredholm.summable_minor`).  `val` version: `val_def`/
  `val_of_ne_zero` + `Real.log` arithmetic: `val (x) = −log‖x‖/−log‖3‖·…` — use
  `PseudoUniformizer.val` API (`val_le_val_iff` etc.) or directly: `‖c_m‖ = ‖3‖^k ⇒
  val = k` (small bridging lemma via `val_def` + `Real.log_pow`; keep as private
  helper).
- **Mathlib**: `Finset.sum_range_id`, `pow_lt_pow_right_of_lt_one`, `Real.log_pow`.
- **Sources**: [Jac Thm 2.12 pp. 34–35], statement + proof quoted in decomposition.md
  R3.  **Generality**: hypothesis "compact" dropped (implied); `h3` necessary.

### [CLEANUP-J5] /cleanup PhD/Jacobs/SlopeTheorem.lean (cadence + final)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J011 | **Type**: cleanup

### [J012] kappaSeries₂ / weightGenFun coefficient API
- **Status**: done (2026-08-03; coeff_kappaSeries₂ = rfl [MvPowerSeries function-type defeq, same as J007's coeff_diagRescale]; dep on J004 was statement-level only. The OPTIONAL convolution helper (coeff of triple product) was NOT extracted — delegated to J013's worker to shape on first contact per the ticket's own conditional; if J013 extracts it, record its name here) | **File**: PhD/Jacobs/U3Data.lean | **Depends**: J004, J005 | **Type**: lemma
- **Decls**: `coeff_kappaSeries₂` (+ any private coeff-convolution helpers the next two
  tickets need: coefficient of a product of three series via `MvPowerSeries.coeff_mul`
  double convolution — extract ONE reusable private lemma
  `coeff_weightGenFun_eq_sum …` here if J013's first attempt wants it)
- **Sketch**: `coeff_kappaSeries₂` is `rfl` (function-type def).  The convolution
  helper: `MvPowerSeries.coeff_mul` twice + `Finsupp.antidiagonal` bookkeeping over
  `Fin 2 →₀ ℕ`; keep the statement in terms of `idx` and finite sums over
  `Finset.range`-boxes (all exponents ≤ the target multidegree).
- **Mathlib**: `MvPowerSeries.coeff_mul`, `Finsupp.antidiagonal` API.
- **Sources**: [Jac p. 29 Prop 2.6 display].  **Generality**: n/a (project-local).

### [J013] **Lemma 2.7**: integrality of `h₀,₂`, `h₁,₂`
- **Status**: done (2026-08-03, worker; both targets proved via a reusable PRIVATE tower in U3Data.lean lines ~149-545: `RowInt φ := ∀ p, ‖coeff p φ‖ ≤ ‖3‖ ^ p 0` with monomial/add/neg/sub/mul closure + KEY `rowInt_inv` (strong induction on p 0 + p 1 via MvPowerSeries.coeff_inv, needs ‖constantCoeff‖ = 1); ν-VALUATION TABLE: norm_nu/nu_add_one = 1, nu_sub_one/nu_add_two ≤ ‖3‖, nu_sub_four ≤ ‖3‖², three_mul_nu_add_two = 1 (all from hνc via norm_num factorisations 2695=5·7²·11, 2694=3·898, 2697=3·899, 2691=9·299, 2700=27·100); uniform `rowInt_weightGenFun (hd: ‖d‖=1) (hd1: ‖d−1‖≤‖3‖) (hc: ‖c‖≤‖3‖²) (ha: ‖a‖≤‖3‖) (hb: ‖b‖≤1)`; also in-file `norm_unitPow_le_one`, `norm_binomialCoeff_mul_pow_le (he: ‖e‖ ≤ ‖3‖²)`. ADVERSARIAL FINDING: the κ-bound genuinely needs ‖c/d‖ ≤ ‖3‖² (fails from n=2 with only ≤ ‖3‖) — data satisfies it exactly. AXIOM NOTE: targets carry sorryAx transitively through STILL-SORRIED norm_unitPow_sub_one_le (J003/J004 debt, authorised); clears automatically when J003/J004 land. NOTE for J018: tower is private to U3Data — Slopes.lean work must de-privatise or lift. Verified 0 errors, 8 sorries remain (2.11 ×4 + M22 ×4)) | **File**: PhD/Jacobs/U3Data.lean | **Depends**: J012 | **Type**: theorem (computational, LARGE)
- **Decls**: `norm_coeff_h02_le`, `norm_coeff_h12_le`
- **Sketch**: Entry-valuation table (verify each from `hνc` by `norm_num`-style
  congruence arithmetic; decomposition.md finding 4): for every matrix in play,
  `‖a‖ ≤ ‖3‖`, `‖b‖ ≤ 1`, `‖c‖ ≤ ‖3‖²`, `‖d‖ = 1 = ‖d⁻¹‖`.  Inverse series:
  `(linSeries γ)⁻¹` has `(j,0)`-coefficient of norm `≤ ‖c/d‖^j ≤ ‖3‖^{2j}` (geometric
  expansion — prove by the recurrence for `MvPowerSeries.inv` or directly:
  `lin⁻¹ = d⁻¹·∑ (−c/d)^n xⁿ` verified by multiplying out); `(quadSeries γ)⁻¹`
  `(j,i)`-coefficient: expand `(d + cx − axy − by)⁻¹ = d⁻¹ ∑ ((−cx+axy+by)/d)^n`;
  each `x` in a monomial arrives with `c` (`‖3‖²`) or `a` (`‖3‖`) ⇒ norm ≤ `‖3‖^j`.
  κ-factor: `x^n`-coefficient norm ≤ `‖(c/d)^n·binom‖ ≤ ‖3‖^{2n}·‖t‖-ish` (J004; for
  n ≥ 1 even the crude `≤ ‖3‖^n` suffices — don't over-optimise).  Convolve (J012
  helper): every `x`-degree-m coefficient ≤ `max` over splittings of `∏ ‖3‖^{mₖ}` =
  `‖3‖^m`.  Norm-≤-1 for y-only factors keeps the rest bounded by 1.
- **Mathlib** (VERIFIED 2026-08-03 in Mathlib/RingTheory/MvPowerSeries/Inverse.lean):
  `MvPowerSeries.mul_inv_cancel (φ) (h : constantCoeff φ ≠ 0) : φ * φ⁻¹ = 1` (and
  `inv_mul_cancel`), `coeff_inv` (the recurrence — use it for the coefficient bounds by
  strong induction on the multidegree), `invOfUnit_eq (φ) (h : constantCoeff φ ≠ 0)`,
  `constantCoeff_inv`.  Alternative: exhibit the explicit geometric inverse and identify
  it via `mul_inv_cancel` + `MvPowerSeries.eq_inv_of...`/uniqueness-of-inverse in the
  ring (`inv_eq_of_mul_eq_one_right` works in any monoid once both cancels are known).
- **Sources**: [Jac Lemma 2.7 p. 30] (quoted).  Source proof is 4 lines ("simply a case
  of checking") — honest Lean cost is the convolution bookkeeping; expect the first
  genuinely long proof (~150–250 LOC with the J012 helper).
- **Generality**: stated for the two blocks the milestone consumes; the other four
  h's are AG-W scope (same proof shape — extract the per-matrix lemma with the
  valuation table as hypotheses so AG-W reuses it).

### [J014] **Lemma 2.11**: the commutation identities (data validation)
- **Status**: done (2026-08-04, worker; ALL FOUR identities proved, axioms standard. DATA VALIDATED BY MACHINE: the erratum-corrected eps12M2 a-entry (−5ν/14−5/7) is precisely what closes identities 3-4 — the thesis's printed −15/14 would break both; finding 2's sign issue never surfaces (denominators computed). Scale factors: first chain s = −8 (κ-product (−1/2)·(−8) = 4), first' s = 1 on the nose, second s = −8 both summands (κ-product (1/4)·(−8) = −2), second' s = 1 both. New Rescale section (19 helpers, NOW DE-PRIVATISED 2026-08-04 by orchestrator for J018): substitution calculus diagRescale_zero/sub/monomial, constantCoeff_diagRescale, diagRescale_inv [UNCONDITIONAL — 0-case is 0=0, better than planned], rescaleMat + apply lemmas, diagRescale_linSeries/quadSeries/kappaSeries₂, HEADLINE diagRescale_weightGenFun : dR α β (weightGenFun t γ) = weightGenFun t (rescaleMat α β γ); homogeneity linSeries_smul/quadSeries_smul/kappaSeries₂_smul, HEADLINE weightGenFun_smul : weightGenFun t (s • γ) = (unitPow t s * s⁻¹ * s⁻¹) • weightGenFun t γ [hyps h3, ‖t‖≤1, s≠0, ‖s−1‖≤‖3‖, ‖d−1‖≤‖3‖]) | **File**: PhD/Jacobs/U3Data.lean | **Depends**: J012, J004 | **Parallel**: yes (with J013) | **Type**: theorem
- **Decls**: `lemma211_first`, `lemma211_first'`, `lemma211_second`, `lemma211_second'`
- **Sketch**: per identity, both sides are sums of `weightGenFun`-terms; match
  term-by-term (the pairing is: first↔first, second↔second as in decomposition.md
  finding 1's hand-check).  Per term: (a) `diagRescale` of a `weightGenFun` =
  `weightGenFun` of the entry-rescaled matrix — prove ONE lemma
  `diagRescale α β (weightGenFun t γ) = scalar • weightGenFun t γ'` where
  `γ' = (αβ·a, β·b; α·c, d)` — DERIVED and partially banked 2026-08-03: GenFun.lean now
  has PROVED `diagRescale_mul` (rescale is multiplicative — exponents add across
  convolution; proof via Finset.mem_antidiagonal [generic, NOT Finsupp-namespaced] +
  Finsupp.add_apply-rfl) and `diagRescale_one` (@[simp]).  Remaining for this ticket:
  `diagRescale α β (φ⁻¹) = (diagRescale α β φ)⁻¹` for unit-constant φ (route:
  diagRescale_mul + MvPowerSeries.mul_inv_cancel + constant-coeff preservation
  [p = 0 coefficient is fixed by diagRescale] + an eq-inverse uniqueness step — search
  `MvPowerSeries` for `eq_inv_iff_mul_eq_one`-shape or derive: ψ·φ = 1 → ψ = ψ·(φ·φ⁻¹)
  = (ψ·φ)·φ⁻¹ = φ⁻¹ by ring associativity, needs only mul_inv_cancel), then
  `diagRescale (linSeries γ) = linSeries γ'`, `diagRescale (quadSeries γ) = quadSeries γ'`
  (coefficientwise, C/X simp set), and the kappaSeries₂ rescale law
  `diagRescale α 1 (kappaSeries₂ t c d) = kappaSeries₂ t (α*c) d`-shape (coeff_kappaSeries₂
  both sides + (α c)/d = α·(c/d) + mul_pow).  (b) match the two `weightGenFun`s: linear
  factors are proportional (`lin₂ = s·lin₁`), quadratics too (same `s`); then
  `κ-parts`: `kappaSeries₂ t (s·c) (s·d) = unitPow t s • kappaSeries₂ t c d`-type
  lemma — needs `unitPow_mul` (J004) + `(s·c)/(s·d) = c/d`.  (c) collect scalars and
  close by `ring`-style field arithmetic (the `−8`-rescale bookkeeping of finding 1).
  **If any identity refuses: STOP, suspect the data entry (decomposition.md findings
  1–3), re-check against the thesis's §B code, and only then escalate.**
- **Mathlib**: field `ring`/`field_simp` in `K`; `MvPowerSeries` mul/smul coeff lemmas.
- **Sources**: [Jac Lemma 2.11 p. 33] (quoted; note the thesis's second chain has a
  typo "h₁,₂(7x/10, x, y)" — read "h₁,₂(7x/10, y)").
- **Generality**: exactly the thesis's identities; they double as the machine
  cross-check of the transcribed data (adversarial design).

### [CLEANUP-J6] /cleanup PhD/Jacobs/U3Data.lean (cadence after 3rd file ticket)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J012, J013, J014 | **Type**: cleanup

### [J015] The `M₂,₂` operator package
- **Status**: done (2026-08-04, same worker as J014; all 4 targets proved; matrixCoeff_M22op = term-mode matrixCoeff_ofGenFun; norm_coeff_smul_diagRescale_le helper; axioms standard, NO transitive debt (J004 landed mid-run). U3Data.lean COMPLETE (0 sorries) — four of five files fully proved) | **File**: PhD/Jacobs/U3Data.lean | **Depends**: J013, J006, J008, CLEANUP-J6 | **Type**: lemma
- **Decls**: `norm_coeff_M22genFun_le`, the column-decay `sorry` inside `M22op`,
  `matrixCoeff_M22op`, `isCompactoid_M22op`
- **Sketch**: `norm_coeff_M22genFun_le`: `coeff` of sum/smul; `‖ω²‖ = 1` (needs
  `norm_omega` — import note: it lives in Slopes.lean's Omega section; MOVE the three
  omega lemmas to U3Data.lean during this ticket if the import direction demands it,
  updating the board), `‖unitPow t 4‖ ≤ 1` (from `norm_unitPow_sub_one_le` + ultrametric
  `‖1 + small‖ = 1`), `coeff_diagRescale` with `‖7/4‖ = ‖7/10‖ = 1` (J001 coprime),
  then J013 bounds.  Column decay for `M22op`: `hyps_of_row_decay` (J006) with
  `c = 1, q = 3` (massage `‖1‖·‖3‖^j`).  `matrixCoeff_M22op` = `matrixCoeff_ofCoeffs`.
  `isCompactoid_M22op` = `isCompactoid_of_row_decay` + `matrixCoeff_M22op`.
- **Mathlib**: as cited.  **Sources**: [Jac (2.1.14) p. 34; Lemma 2.7].
- **Generality**: n/a.

### [CLEANUP-J7] /cleanup PhD/Jacobs/U3Data.lean (final)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J015 | **Type**: cleanup

### [J016] Cube-root-of-unity arithmetic
- **Status**: done (2026-08-03; sq via `linear_combination 4*hω`; norm via ← norm_pow + norm_neg; norm_omega via ω³=1 [`linear_combination (ω-1)*hω`] + nlinarith with sq_nonneg (‖ω‖±1) hints; first-compile) | **File**: PhD/Jacobs/Slopes.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Decls**: `sq_two_omega_add_one`, `sq_norm_two_omega_add_one`, `norm_omega`
- **Sketch**: `(2ω+1)² = 4(ω²+ω)+1 = −4+1 = −3` by `linear_combination 4*hω`.
  Norms: `‖(2ω+1)‖² = ‖(2ω+1)²‖ = ‖−3‖ = ‖3‖` (`norm_mul`/`norm_pow`, `norm_neg`).
  `norm_omega`: `ω³ = 1` (`linear_combination (ω−1)*hω`), `‖ω‖³ = 1`,
  positivity ⇒ `‖ω‖ = 1` (`pow_left_injective`-style on ℝ≥0 / `Real` monotone).
- **Mathlib**: `linear_combination`, `norm_pow`, `norm_neg`.
- **Sources**: [Jac p. 32] (`ω = (−1+√−3)/2`).  **Generality**: char-0 field only.

### [J018] **Theorem 2.14** (THE CRUX): `H′₂,₂(x/3, y) ≡ −1/(1−xy) mod 𝔪₃`
- **Status**: done (2026-08-04, worker; PROVED, axiom-clean; Slopes.lean 139→1160 lines, 49 private helpers incl. the NormLe ε-calculus with 1st/2nd-order inverse expansions. PLAN CORRECTION (load-bearing, recorded): rescaled b,c entries are NOT negligible — scalars Cₖ have norm ‖3‖^{-1/2} so errors must go below ‖3‖^{1/2}, and v₃(c₂) = 1/2 EXACTLY (my estimate dropped v₃(48) = 1), v₃(b₁) = 1/2; their θ-linear contributions cancel BETWEEN the three terms via the ring identity `ω·appr₁ + appr₂ + appr₃ + θ·Q = θ(1−ω)(Q+yQ²) − 6x²Q² − 3xyQ²` from ω+2+ωθ = 2(ω²+ω+1) = 0 and θ²+3 = 0 (θ = 2ω+1). NUMERIC RESIDUES (mod 𝔪₃): γ₁ ≡ (1,−θ;0,1), γ₂ ≡ (1,θ;−θ,1), γ₃ ≡ (1,0;θ,1); a₁/d₁ = −(ν−1)/(3(ν+1)) ≡ 1, a₂/d₂ = −ν/(3ν+2) ≡ 1, a₃/d₃ = −(ν+2)/(3ν) ≡ 1; C₁ ≡ ω/θ, C₂ = C₃ ≡ 1/θ. New ν-congruences: ‖ν−13‖ ≤ ‖3‖² (2682 = 9·298), ‖ν+14‖ ≤ ‖3‖² (2709 = 9·301), ‖7ν+116‖ ≤ ‖3‖³ (18981 = 27·703). Quantitative: every coeff of NgenFun − negGeom has norm ≤ max ‖t‖ ‖2ω+1‖. hν2 NOT needed for J017/J018 (linter-confirmed) — only hνc) | **File**: PhD/Jacobs/Slopes.lean | **Depends**: J004, J012, J013, J016 | **Type**: theorem (VERY LARGE)
- **Decls**: `norm_coeff_NgenFun_sub_negGeom_lt`
- **Sketch** (mirrors [Jac pp. 36–39]; full sub-decomposition in decomposition.md L5.2):
  1. κ-estimates ((i)): each κ-factor `= 1 + err`, `‖err‖ ≤ ‖t‖‖3‖^{1/2}`-class —
     instances of J004's two bounds at the entry table.
  2. Collection ((ii)): work with the 3-term sum over the common denominator; after the
     `x ↦ x/(3(2ω+1))`, `y ↦ (2ω+1)y` rescale, prove coefficientwise: survivors of
     norm 1 are exactly the `a`-diagonal `(xy)^m` chain with the sign/scalar
     `−1/(ω(2ω+1))`-bookkeeping landing on `−1`; all else `< 1`.  Route (a)
     certificate-style (exhibit the `3⁶(2ω+1)`-decomposition, `norm_num` over
     `ℤ[ν,ω]`, `ν ↦ 2695 + 3¹⁰s`, `ω² ↦ −ω−1`) or route (b) per-coefficient-class
     from the valuation table — worker's choice; the thesis's pp. 37–38 displays are
     the verification anchor for route (a).
  3. Endgame ((iii)): `(1−xy)(1+xy+x²y²) = 1−x³y³` by `ring` in the polynomial ring,
     transported through the inequality phrasing (the `negGeom` inverse's coefficients
     are `−1` on `(xy)^m`, `0` else — small lemma: `(1 − X0X1)·(∑ (X0X1)^m) = 1`).
  **Before starting: consider `/develop --continue` to split this ticket into named
  private sub-lemmas once J013's proof style has settled** — the board pre-authorises
  that split (no scope change).  If a coefficient identity FAILS numerically: check
  decomposition.md findings 1–3 (data errata) before anything else; if data is clean,
  hard-stop B1 with the failing coefficient as evidence.
- **Mathlib**: `ring`, `linear_combination`, `norm_num` extensions; `Finset` convolution
  sums (J012 helper).
- **Sources**: [Jac Thm 2.14 statement p. 36; proof pp. 36–39] (structure quoted in
  decomposition.md R5).  ~3 source pages ⇒ largest ticket of the board.
- **Generality**: exactly the thesis's disc; the `λ ∈ {1,2}` variants are AG-EXT.

### [J017] Lemma 2.13 (integrality of `N`)
- **Status**: done (2026-08-04, same worker; via norm_le_of_sub + normLe_negGeom from J018, as planned) | **File**: PhD/Jacobs/Slopes.lean | **Depends**: J018 | **Type**: lemma
- **Decls**: `norm_coeff_NgenFun_le`
- **Sketch**: `‖N_p‖ ≤ max(‖N_p − G_p‖, ‖G_p‖) ≤ max(<1, ≤1) ≤ 1` where `G = negGeom`
  (coefficients 0/−1).  One `norm_sub_norm_le`/ultrametric max step + the `negGeom`
  coefficient lemma from J018(iii).  (Thesis: "The result will follow from our proof of
  Theorem 2.14" — same dependency direction.)
- **Sources**: [Jac Lemma 2.13 p. 36].

### [J019] Corollary 2.15: unit minors
- **Status**: done (2026-08-04, same worker; B = (−1)•1, entrywise-close determinant lemma norm_det_sub_det_le [+ norm_prod_sub_prod_le telescoping], isosceles norm_eq. geomFun/coeff_negGeom helpers public-worthy for AG-NP later) | **File**: PhD/Jacobs/Slopes.lean | **Depends**: J018 | **Type**: lemma
- **Decls**: `norm_det_NgenFun_minor`
- **Sketch**: entries `≡ −δ_{ji} mod 𝔪₃` (J018 + `negGeom`-coeff at `idx j i`:
  `−1` iff `j = i`).  `det` congruence: `det A − det(−1) = ∑` of products each
  containing a `< 1` factor with the rest `≤ 1` — do it by the Leibniz sum, or slicker:
  multilinearity column-by-column replacement telescoping (`Matrix.det`-congruence
  lemma search: `Matrix.det_eq_of_forall…`? likely absent — private lemma:
  `‖det A − det B‖ < 1` if entrywise `‖A−B‖ < 1` and `‖A‖,‖B‖ ≤ 1`, by telescoping).
  `‖det(−1 : Matrix (Fin n))‖ = ‖(−1)^n‖ = 1`; ultrametric equality-of-norms.
- **Sources**: [Jac Cor 2.15 p. 36] (quoted).

### [CLEANUP-J8] /cleanup PhD/Jacobs/Slopes.lean (cadence after 3rd file ticket)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J016, J018, J017 | **Type**: cleanup

### [J020] The trace-property conjugation step
- **Status**: done (2026-08-04, worker; public `ext_matrixCoeff` (operators equal iff matrices equal — via cSpace.hasSum_single + HasSum.mapL + HasSum.unique) + matrixCoeff_smul/-diagOp_comp_left/-comp_diagOp helpers; charCoeff_conj_eq via charPowerSeries_comm; ACCEPTED DEVIATION (orchestrator sign-off, b2_log): M22half's body guarded `if hcube : ω^2+ω+1=0 then ofGenFun … else 0` — the def's signature carried no hω so the boundedness hole was genuinely false for wild ω; junk-value idiom, matrixCoeff_M22half is the interface, all downstream statements carry hω; no theorem statement text changed) | **File**: PhD/Jacobs/Slopes.lean | **Depends**: J015, J008, J010 | **Type**: theorem
- **Decls**: `M22half`'s two hypothesis sorries, `charCoeff_conj_eq`, `charCoeff_M22op_eq`
- **Sketch**: `M22half` bounds: rows of `diagRescale (2ω+1)⁻¹ 1 H₂,₂` have norm
  `≤ ‖(2ω+1)⁻¹‖^j·‖3‖^j = (‖3‖^{1/2})^j` (squared arithmetic via J016) — row decay ⇒
  both hypotheses (J006).  `charCoeff_conj_eq`: `TateFredholm.charPowerSeries_comm`
  (read its exact hypotheses at `Fredholm.lean:756` — likely `IsCompactoid u`) with
  `u = M22half`, `v = diagOp ((2ω+1)^·)` (`‖(2ω+1)^n‖ ≤ 1`); operator equalities
  `v.comp u = M22op` and the displayed composite by `matrixCoeff`-ext (J008's
  composition lemma + `ContinuousLinearMap.ext` via `exists_coeffEquiv`-style
  injectivity — small lemma: operators with equal `matrixCoeff` are equal, from
  J006's construction or TateFredholm's `exists_coeffEquiv`).  `charCoeff_M22op_eq`:
  previous + `charCoeff_smul` (J010) unwinding `NgenFun`'s scalar.
- **Mathlib**: `ContinuousLinearMap.ext`.  **Sources**: [Jac p. 36] ("we invoke
  Proposition 1.14: let u = D(1/(2ω+1))M₂,₂ and v = D(2ω+1)…", quoted in
  decomposition.md R5 step 1).

### [CLEANUP-ALL-1] /cleanup-all over PhD/Jacobs (pre-milestone; board `.mathlib-quality/jacobs/`)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: CLEANUP-J2, CLEANUP-J4, CLEANUP-J5, CLEANUP-J7, J019, J020 | **Type**: cleanup

### [J021] **MILESTONE — Corollary 2.16**: `v₃(cₘ(M₂,₂)) = m²/2` (vertex data for slopes `1/2, 3/2, 5/2, …`)
- **CAVEAT (user-flagged 2026-08-04)**: this valuation identity gives the Newton-polygon
  POINTS `(m, m²/2)`, not the slope statement itself — the reading "hence the slopes are
  `1/2, 3/2, …`" is the separate AG-NP step (independent, later). Docstrings must not
  overclaim; see SlopeTheorem.lean's module-header note for the wording pattern.
- **Status**: done (2026-08-04, worker; MILESTONE PROVED: sq_norm + val forms via norm_charCoeff_of_unit_minors on the (ωθ)⁻¹-scaled conjugate [hdiv from J017, hmin from J019, coeff_M22scaledGenFun_eq : coeff = 3^j·coeff NgenFun], charCoeff_smul, ‖θ‖²=‖3‖, ‖ω‖=1, m + 2·C(m,2) = m²; val by Real.log of the squared identity. AXIOMS INDEPENDENTLY VERIFIED by orchestrator: [propext, Classical.choice, Quot.sound] exactly; PROJECT-WIDE 0 SORRIES confirmed. NB CLEANUP-ALL-1 dep was reordered after the fact — cleanups now run as the consolidated post-milestone wave) | **File**: PhD/Jacobs/Slopes.lean | **Type**: theorem (milestone)
- **Decls**: `sq_norm_charCoeff_M22op`, `val_charCoeff_M22op`
- **Sketch**: Let `u′` be the `ofGenFun` of the conjugated series (from J020's RHS) and
  `N`-operator its `D(1/3)`-rescale reading.  Apply J011 to the operator whose matrix is
  `NgenFun`-row-based: hypotheses `hdiv` from J017 re-based (`matrixCoeff = coeff ∘ idx`,
  J015-style; the `3^j` re-insertion is `diagRescale` bookkeeping) and `hmin` from J019.
  Then `charCoeff_M22op_eq` (J020) + `charCoeff_smul`-arithmetic:
  `‖cₘ(M₂,₂)‖² = ‖ω(2ω+1)‖^{2m}·‖cₘ(scaled)‖² = ‖3‖^m·(‖3‖^{C(m,2)})² = ‖3‖^{m²}`
  (`m + m(m−1) = m²` by `ring`).  `val` form: bridging lemma from J011's val step.
  Run `#print axioms Jacobs.sq_norm_charCoeff_M22op` — standard axioms only.
- **Sources**: [Jac Cor 2.16 p. 39]: "The n-th slope of M₂,₂ is n − 1/2 for n ∈ ℕ.
  Proof. Apply Theorem 2.14 with M = M′₂,₂." (+ the p. 36 scalar-shift remark, both
  quoted in decomposition.md).

### [CLEANUP-FINAL] /cleanup-all, final pass (board `.mathlib-quality/jacobs/`)
- **Status**: done (2026-08-05, consolidated post-milestone wave — see closing summary) | **Depends**: J021 | **Type**: cleanup


---

# AG-NP tranche tickets (opened 2026-08-04; file = PhD/Jacobs/SlopeReading.lean, 13 sorries)

All statements are already in the skeleton (build green); tickets = fill the named sorries.
Read decomposition.md "AG-NP tranche" first (prose proof, approach comparison, attack logs,
verified API citations into PhD/NewtonPolygons/{Spec,SpecConstruction,Height}.lean).

### [N001] `ofSlopes` construction + walk layer
- **Status**: done (2026-08-04, worker; all fields proved inline — junk/final via absurd+simp on ⊤-hypotheses, increasing via WithBotTop.coe_le_coe; vertexX by induction with vertexX_succ; unitSlope via unitSlope_eq_slopes with coe-arith brackets; heightFun via Algebra.algebraMap_self_apply + NewtonPolygon.toReal_coe) | **Depends**: none | **Parallel**: yes | **Type**: def fields + lemma
- **Decls**: the 6 field sorries of `NewtonPolygon₀.ofSlopes`, `vertexX_ofSlopes`,
  `unitSlope_ofSlopes`, `heightFun_ofSlopes`
- **Sketch**: fields: support = ⊤ ⇒ junk/final hypotheses are False (`⊤ ≤ (n : WithTop ℕ)`,
  `(n:WithTop ℕ)+1 = ⊤` — `simp`/`exact absurd … (by simp)`); increasing: coe-mono of hs
  into WithBotTop (find the coe-≤-coe simp lemmas for the project's WithBotTop; worst case
  `WithBot.coe_le_coe`+`WithTop.coe_le_coe` composition). vertexX: `vertexX` def = start.1 +
  Σ range n of (lengths i).map coe = 0 + Σ of 1 = n (`Finset.sum_const`, `WithTop.map`,
  `nsmul`). unitSlope: `unitSlope_eq_slopes (n := j)` (Height.lean:276) with brackets from
  vertexX_ofSlopes (`j ≤ 0 + j < j+1` in WithTop ℤ — coe arith). heightFun: unfold +
  `Finset.sum_congr` over unitSlope_ofSlopes + `NewtonPolygon.toReal` of a real coe
  (find `toReal`-coe simp lemma in Basic.lean:93 region).
- **Sources**: decomposition AG-NP N1 (attacks recorded there; prior-B2 rep-degeneracy
  addressed by support = ⊤ design).

### [N002] `height_ofSlopes`
- **Status**: done (2026-08-04, same worker; KEY REUSABLE ROUTE for N005: private `height_eq_heightFun_of_unitSlope_ne_top (P) (h : ∀ t < c, P.unitSlope t ≠ ⊤) : P.height (start.1 + c) = heightFun c` — built from public Height API only (rightHeight unfold + split_ifs), the ⊤-guard of the walk is exactly a ⊤ incoming unitSlope; then unitSlope_ofSlopes gives ≠⊤ trivially) | **Depends**: N001 | **Type**: lemma (the walk-layer content)
- **Sketch**: first `height ≠ ⊤` on the region: induct on k; k = 0 via the height-at-anchor
  value (find the height-at-start lemma / height_eq_heightFun at 0 with heightFun_zero);
  step: if height (k+1) = ⊤ then by `unitSlope_eq_top_of_height_eq_top`-adjacent
  (Height.lean:542 private — use `height_eq_top_mono` contrapositive or the public
  route: height (k+1) ≠ ⊤ because heightFun is real and `height_eq_heightFun` needs the
  ≠⊤ we're proving — AVOID circularity: use instead whatever direct height-def lemma
  exists (`height_eq_bot_iff`:533 suggests a `height_eq_coe`-style sibling — SEARCH
  Height.lean 500–570 first; if only mono-⊤ exists, prove ≠⊤ by strong induction using
  `unitSlope_ne_top_of_height_ne_top`'s contrapositive chain). Then `height_eq_heightFun`
  + `heightFun_ofSlopes` + push coe.
- **Sources**: decomposition N2; Height.lean 533–620 (read before starting).

### [N003] `isNewtonPolygonOf_ofSlopes` (the spec theorem)
- **Status**: done (2026-08-04, same worker; THE CANONICAL THEOREM OF THE TRANCHE, proved exactly per plan: hpt equality lemma + 4-field refine; isGreatest = isBelow_iff_height + lift-to-ℕ + height_eq_bot_iff at x < 0, five lines — the integer-sampling collapse confirmed in practice. Axioms: standard three, orchestrator-verified) | **Depends**: N002 | **Type**: theorem (core of the tranche)
- **Sketch**: constructor ⟨?, ?, ?, ?⟩ per decomposition prose (ii): start_le by omega on
  `(k:ℤ) < 0`; start_mem := ⟨0, rfl-ish, hv 0 + sum_range_zero⟩; height_le k: rewrite
  `height_ofSlopes` + `pointHeight_coe (hv k)` + `algebraMap ℝ ℝ`-id (`map_id`/
  `RingHom.id_apply` — find the `Algebra.algebraMap_self`-simp) ⇒ le_refl; isGreatest Q hQ0
  hQle: `NewtonPolygon₀.isBelow_iff_height.2` fun x => cases on `0 ≤ x`: x = (k:ℕ) via
  `Int.toNat` (`Int.toNat_of_nonneg`), chain hQle k with height_ofSlopes-equality; x < 0:
  `Q.height x = ⊥` by `height_eq_bot_iff` (Q.starting_point.1 = 0 via hQ0 +
  ofSlopes_starting_point) ⇒ `bot_le`.
- **Sources**: decomposition N3 + [Jac pp. 34–35] quote.

### [CLEANUP-N1] /cleanup PhD/Jacobs/SlopeReading.lean (cadence after 3rd)
- **Status**: done (2026-08-04, merged with CLEANUP-N2 into one post-completion pass — file was already warning-free; 4 docstrings added to the @[simp] projections; no golf needed; gates green) | **Depends**: N003 | **Type**: cleanup (board .mathlib-quality/jacobs/)

### [N004] Admissibility + height transport
- **Status**: done (2026-08-04, worker; affine bound via Finset.card_nsmul_le_sum; transport = one-term height_eq application. API arg-order note — UPDATED 2026-08-04 by the `ϖ₃` refactor, see the API CHANGE banner at the top of this board: `val_charCoeff_of_unit_minors h3 u hdiv hmin m` (h3 FIRST, include order; needs `[CharZero K]`); `val_charCoeff_M22op ω h3 ht hν2 hνc hω m` — the trailing `ϖ hϖ` arguments are GONE) | **Depends**: N003, CLEANUP-N1 | **Type**: lemma
- **Decls**: `isAdmissible_of_partial_sums`, `height_newtonPolygon₀OfSeq_ofSlopes`
- **Sketch**: admissible: `isAdmissible_of_affine_bound (m := s 0) (b := y₀)`; hypothesis:
  for `v k = a`, `a = y₀ + Σ_{i<k} s i` (hv + WithTop.coe injectivity) and
  `s 0 * k + y₀ ≤ y₀ + Σ`: `Σ_{i<k} s i ≥ k • s 0` by `Finset.card_nsmul_le_sum`-family
  (each `s 0 ≤ s i` by `hs (Nat.zero_le i)`; name candidates: `Finset.card_nsmul_le_sum`,
  `Finset.sum_le_card_nsmul`'s dual — verify) + cast arith. transport: 
  `((isNewtonPolygonOf_newtonPolygon₀OfSeq v ⟨0, by simp [hv 0]⟩ (admissible)).height_eq
  (isNewtonPolygonOf_ofSlopes …) x)` — check `IsNewtonPolygonOf.height_eq`'s argument
  order/direction (Spec.lean:101) and flip if needed.
- **Sources**: decomposition N4; SpecConstruction.lean:47 (affine-bound lemma, read).

### [N005] Slope transport (RISK LEAF — two routes)
- **Status**: done (2026-08-04, same worker; NEITHER planned route — a THIRD, construction-level route won, fully general: private `slopes_zero_ne_bot (v) (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) : (newtonPolygon₀OfSeq v).slopes 0 ≠ ⊥` via Height.lean:609 + the ⊥-emitting constructor is uniquely Step.unboundedBelow + Construction.lean:474 `unboundedBelow : ¬ BddBelow (slopeSet …)` contradicting admissibility. NO corner descoping — case A's j = 0 covered by the general theorem. PUBLIC-API candidate for the NP library later) | **Depends**: N004 | **Type**: theorem
- **Decl**: `unitSlope_newtonPolygon₀OfSeq_ofSlopes`
- **Sketch**: Route (a): pin `toReal (unitSlope j)` = height increment: from N004 heights =
  ofSlopes heights (all real); `height_eq_heightFun` on the constructed polygon at j, j+1
  (its heights ≠ ⊤ since equal to real coes) + `heightFun_succ` ⇒ toReal (unitSlope j) =
  s j.  Then exclude junk: ⊤ via `unitSlope_ne_top_of_height_ne_top` (Height.lean:577);
  ⊥ via Height.lean:609 `slopes_zero_eq_bot_of_unitSlope_eq_bot` + show the constructed
  polygon's `slopes 0 ≠ ⊥`: from the spec (`IsNewtonPolygonOf.bddBelow`,
  SpecConstruction.lean:69) / the algorithm's inf-of-bddBelow — SEARCH SpecConstruction
  for a "slopes of newtonPolygon₀OfSeq are real/not-⊥" lemma; if genuinely absent, add
  a small private lemma IN THIS FILE proving `slopes 0 = ⊥ → False` from
  `unitSlope_zero_mul_le`-style spec facts (⊥ first slope would put points below every
  line — contradict a finite point at k = 1). Route (b) fallback if (a)'s ⊥-exclusion
  stalls: close all j with s j ≠ 0 by the toReal-pin alone (toReal ⊥ = toReal ⊤ = 0 ≠
  s j), and handle the single remaining case (case A, j = 0, s 0 = 0) by the first-slope
  minimality analysis; if THAT also stalls, hard-stop with the goal state — the height
  transports (N004) already carry the geometric content and the board can descope this
  leaf's j = 0 corner after user review.
- **Sources**: decomposition N5 (toReal-collapse attack documented — this is why the
  leaf is nontrivial).

### [N006] Case A instantiation (PoC — [Jac Thm 2.12] slopes 0,1,2,…)
- **Status**: done (2026-08-04, same worker; Gauss bridge via Finset.sum_range_id + Nat.choose_two_right + Nat.cast_sum; PowerSeries transport by defeq unfold of newtonPolygon₀OfPowerSeries + charPowerSeries_coeff) | **Depends**: N003 (isNewtonPolygonOf part), N005 (unitSlope part) | **Type**: theorem
- **Decls**: `isNewtonPolygonOf_val_charCoeff`,
  `unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries`
- **Sketch**: hv: `val_charCoeff_of_unit_minors` (SlopeTheorem, proved) gives
  `(ϖ₃ h3).val (charCoeff u m) = (m.choose 2 : ℝ)`-coe (spelling updated by the `ϖ₃` refactor
  — see the API CHANGE banner at the top of this board); bridge `(∑ i ∈ range m, (i:ℝ)) =
  (m.choose 2 : ℝ)`: cast `Finset.sum_range_id_mul_two` + `Nat.choose_two_right` (+ push_cast
  + linarith), `zero_add`.  PowerSeries form: `coeffSeq (ϖ₃ h3).val (charPowerSeries u) =
  fun m => (ϖ₃ h3).val (charCoeff u m)` by funext + `coeffSeq` unfold + `charPowerSeries_coeff`;
  then N005-instance rewritten along that funext (`newtonPolygon₀OfPowerSeries` unfolds to
  `newtonPolygon₀OfSeq (coeffSeq …)` — check PowerSeries.lean:52/58).
- **Sources**: decomposition N6.

### [N007] Case B instantiation ([Jac Cor 2.16] slopes 1/2, 3/2, …)
- **Status**: done (2026-08-04, same worker; sum_add_distrib + own add_two_mul_choose_two copy (Slopes.lean's is private) + linarith. ALL 7 AG-NP proof tickets axiom-clean (verbatim check in worker report); SlopeReading.lean 0 sorries) | **Depends**: N006 | **Type**: theorem
- **Decls**: `isNewtonPolygonOf_val_charCoeff_M22op`, `unitSlope_newtonPolygon₀OfPowerSeries_M22op`
- **Sketch**: as N006 with s j = (j:ℝ) + 1/2; hv from `val_charCoeff_M22op` (Slopes,
  proved; RHS `((m^2:ℝ)/2 : WithTop ℝ)`-shaped — match coercions); bridge
  `∑_{i<m}((i:ℝ) + 1/2) = (m^2:ℝ)/2`: `Finset.sum_add_distrib` + N006's Gauss bridge +
  `Finset.sum_const` + push_cast + ring.
- **Sources**: decomposition N7.

### [CLEANUP-N2] /cleanup PhD/Jacobs/SlopeReading.lean (final)
- **Status**: done (2026-08-04, see CLEANUP-N1; axioms on all three endpoints exactly standard, build green, 0 sorries)

## AG-NP TRANCHE COMPLETE (2026-08-04, planned + executed same day)
All 7 proof tickets + cleanups done. SlopeReading.lean: 0 sorries, 0 warnings, standard
axioms on every endpoint. Canonical result: `isNewtonPolygonOf_ofSlopes` (spec-level, per
the user's canonicality rationale); corollaries: the constructed Newton polygons of
`det(1−Tu)` (Thm 2.12 hypotheses) and `det(1−T·M₂,₂)` have unit slopes 0,1,2,… resp.
1/2,3/2,5/2,….  PUBLIC-API CANDIDATES for the NewtonPolygons library (note for a future
coordination pass, not acted on): `height_eq_heightFun_of_unitSlope_ne_top` (dedupe with
SpecConstruction's internal copy → Height API), `slopes_zero_ne_bot` (construction-level
⊥-exclusion under IsAdmissible), `coe_toReal_eq_self` (WithBotTop round-trip).  Remaining
open seams: AG-B (blocked on QMF T016/T017), AG-W, AG-EXT. | **Depends**: N007 | **Type**: cleanup


---

# AG-W tranche tickets (opened 2026-08-04; files = PhD/Jacobs/BlockOp.lean, DiamondW.lean; 40 sorries)

Skeleton canonical (build green); read decomposition.md "AG-W tranche" first (source
quotes, hand-checks, errata 6–7, per-leaf attack notes).  General material (BlockOp)
sits in namespace TateFredholm at TateFredholm generality — keep it Jacobs-free.

### [W001] Subtype restriction + reindex machinery
- **Status**: done (2026-08-05, two workers across the pause; Aux layer [ofTendsto/comap/GENERIC ext_matrixCoeff/matrixCoeff_sum/tendsto_cofinite_prod_of_finite] + Subtype/Reindex sections; projSubtype = one-line comap; AMENDMENT ACCEPTED+b2-logged: isCompactoid_restrictOp carries [IsTate R] — false without, counterexample in b2_log) | **File**: PhD/Jacobs/BlockOp.lean | **Depends**: none | **Parallel**: yes | **Type**: def+lemma
- **Decls**: `cSpace.inclSubtype`, `cSpace.projSubtype`, `matrixCoeff_inclSubtype`,
  `restrictOp` spec `matrixCoeff_restrictOp`, `isCompactoid_restrictOp`, `reindexOp`,
  `matrixCoeff_reindexOp`, `isCompactoid_reindexOp`
- **Sketch**: READ TateFredholm's extendZero machinery first (Fredholm.lean:979 region +
  whatever constructions it exposes) and ModelSpace's cSpace API (single, norm, C₀ realisation
  `C₀(Ix I, R)`).  inclSubtype: extension by zero — coordinatewise `fun x => if h : p x then
  f ⟨x, h⟩ else 0`, C₀-membership from f's (preimage of cofinite), linearity/norm-1-bound ⇒
  CLM (`LinearMap.mkContinuous`).  projSubtype: restriction — coordinatewise, norm-≤-1.
  reindexOp: conjugate by the C₀-composition equiv along `Ix`-transported `e` (or
  coordinatewise like ofCoeffs).  Specs by `matrixCoeff` unfold + `single`-images
  (inclSubtype (single i 1) = single i.1 1 etc.).  isCompactoid transports: rowNorms of
  restrictions/reindexes are sub-sups of the originals'.
- **Sources**: [Ser62 Lemme 2] setting; construction-level (no thesis content).
- **Generality**: TateFredholm block (NormedCommRing+ultra+complete+NormOneClass; NB
  NormOneClass needed only where Fredholm needs it — minimise per-decl if free).

### [W002] Block operators
- **Status**: done (2026-08-05; blockIncl/blockProj + orthogonality + KEY blockOp_blockIncl collapse (blockOp T ∘ incl_b = Σ_a incl_a ∘ T a b); blockOp_comp proved; isCompactoid_blockOp carries [IsTate R] per the same amendment; 12 helpers total — W004/W005/W007-W009 consume blockOp_blockIncl + matrixCoeff_sum. Deprecation notes: _root_.sum_apply, tendsto_finsetSum) | **File**: PhD/Jacobs/BlockOp.lean | **Depends**: W001 | **Type**: def+lemma
- **Decls**: `blockOp`, `matrixCoeff_blockOp`, `blockCorner`, `matrixCoeff_blockCorner`,
  `blockCorner_blockOp`, `isCompactoid_blockOp`, `blockOp_comp`
- **Sketch**: blockOp := Σ_{a,b} incl_{(·.1 = a)-reindexed} ∘ T a b ∘ proj — OR direct
  coordinatewise construction ((blockOp T f) (a, j) = Σ_b (T a b (f (b, ·)-column)) j —
  the finite-sum-of-CLMs route: define per-(a,b) the conjugate `embed a b (T a b) :
  c(σ×I) →L c(σ×I)` via W001's incl/proj along {x // x.1 = b} ≃ I, and sum over the
  Fintype).  blockCorner := reindexOp ∘ restrictOp at (·.1 = a).  Specs from W001's.
  Compactoid: rowNorm (a,j) ≤ max_b rowNorm-of-block ⇒ cofinite decay (finite σ).
  blockOp_comp: matrixCoeff-ext (ADD a generic-index `ext_matrixCoeff` here — the
  ℕ-version's proof in Slopes.lean:1137 (cSpace.hasSum_single + HasSum.mapL + unique)
  generalises verbatim; authorised skeleton amendment, log in report) + composition
  matrixCoeff formula (finite b-sum: `matrixCoeff (u.comp v) (a,j) (c,i) = Σ_b …` via
  the single-expansion).
- **Sources**: assembly device (no thesis content).  **Generality**: as W001.

### [W003] charPowerSeries under reindexing
- **Status**: done (2026-08-05; minor_reindexOp helper + Matrix.det_submatrix_equiv_self + Equiv.finsetCongr + Equiv.tsum_eq [NB: named (α := …) arg BREAKS it — positional only] + Function.Surjective.range_comp for the conditionally-complete iSup; std axioms on all 28 checked decls) | **File**: PhD/Jacobs/BlockOp.lean | **Depends**: W001 | **Parallel**: yes (with W002) | **Type**: lemma
- **Sketch**: `charCoeff` = tsum of minors over Finsets; bijection `Finset I ≃ Finset J`
  by `Finset.map e.toEmbedding` preserves card; per-S minors equal via `Matrix.det_reindex`
  (verify exact name: `Matrix.det_reindex_self`-family / `det_submatrix_equiv_self`) on the
  subtype-equiv `S ≃ S.map e`; conclude tsum-eq by `Equiv.tsum_eq`; lift to charPowerSeries
  by `PowerSeries` ext.
- **Sources**: standard invariance; consumed by W5.

### [W004] **Serre's partition lemma** ([Jac Lemma 1.15] = [Ser62] Lemme 2)
- **Status**: done (2026-08-05, worker; proved EXACTLY per upgraded ticket: twoBlockTriangular_det UNPRIMED orientation matched htri (mathlib M i j row/col agrees with matrixCoeff u j i — no flip); det_toSquareBlockProp_eq via det_submatrix_equiv_self on hand-built subtype-of-subtype equivs; convolution via finsetSplit Equiv + if-truncated HasSum.mul + Function.Injective.hasSum_iff along splitEmbedding + hasSum_sum + Finset.sum_eq_single; PowerSeries.coeff_mul + pow_add;ring signs. [IsTate R] ADDED per accepted amendment (inherited from summable_minor) — W011 consumers supply the instance. 12 private helpers; TRAPS logged: Finset.mul_prod_erase rw fails higher-order (exact with explicit f); S.2-rw motive issues (omega on atoms); trailing rfl past let-bound equivs. Std axioms verbatim) | **File**: PhD/Jacobs/BlockOp.lean | **Depends**: W001 | **Type**: theorem (LARGE, core)
- **Decl**: `charPowerSeries_partition`
- **VERIFIED DISCHARGE UPGRADE (orchestrator, 2026-08-05, while wave 1′ ran)**: mathlib has
  `Matrix.twoBlockTriangular_det (M) (p) [DecidablePred p] (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
  M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det` AND the
  primed orientation `twoBlockTriangular_det'` (h : p i → ¬p j → M i j = 0)
  (Mathlib/LinearAlgebra/Matrix/Block.lean:267/278, statements read this session) — the
  per-minor factorisation is a DIRECT application (choose the orientation matching htri;
  identify our subtype-minor with `toSquareBlockProp` by `Matrix.det`-congruence /
  `equiv_block_det`, also in that file). Step (1) below simplifies accordingly; also
  verified: `Matrix.det_submatrix_equiv_self` (Determinant/Basic.lean:224),
  `Matrix.det_reindex_self` (:252), `PowerSeries.coeff_mul` (PowerSeries/Basic.lean:249).
- **Sketch**: per decomposition W4: (1) per-minor factorisation: for S : Finset I split
  S₁ := S.filter p, S₂ := S.filter (¬p ·); the minor matrix, reindexed along
  `S ≃ S₁ ⊕ S₂`-shaped equiv (`Finset.filter`-partition equiv; `Matrix.det_reindex`),
  is `Matrix.fromBlocks A B 0 D` (zero block = htri) ⇒ `Matrix.det_fromBlocks_zero₂₁`
  (verify name; mathlib has det_fromBlocks_zero₂₁ : det (fromBlocks A B 0 D) = det A *
  det D) ⇒ det(minor S) = det(minor_p S₁)·det(minor_¬p S₂) where the sub-minors are
  matrixCoeff_restrictOp-matrices ✓ W001 spec.  (2) charCoeff convolution:
  c_n(u) = ±Σ_{|S|=n} det = ±Σ_{n₁+n₂=n} (Σ_{|S₁|=n₁ in p})(Σ_{|S₂|=n₂ in ¬p}) — the
  index bijection {S : |S| = n} ≃ Σ_{n₁+n₂=n} {S₁} × {S₂} (Finset partition; build as an
  explicit Equiv); tsum rearrangement over it (`Equiv.tsum_eq`) then `tsum_prod`/
  `Summable.tsum_mul_tsum`-of-norm-summable (summable_minor supplies both factors and
  the product family — mirror Fredholm.lean's own summability patterns); signs: (−1)^n =
  (−1)^{n₁}(−1)^{n₂} ✓.  (3) assemble as `PowerSeries.coeff_mul` convolution identity.
  Mind charCoeff's EXACT def shape (read Fredholm.lean:155 region first).
- **Sources**: [Ser62] Lemme 2 (verbatim quote in decomposition); [Jac Lemma 1.15].
- **Generality**: full TateFredholm; the compactness of restrictions is W001's (Serre's
  "u′ and u″ are compact" — separate leaf, already split ✓).

### [CLEANUP-W1] /cleanup PhD/Jacobs/BlockOp.lean (cadence after 3rd)
- **Status**: done (2026-08-05, consolidated closing wave — see AG-W closing note) | **Depends**: W002, W003, W004 | **Type**: cleanup

### [W005] Block-diagonal product
- **Status**: done (2026-08-05, same worker; PRIMARY route (Fintype.card induction via universe-explicit aux, split at ·.1 = a₀, reindex-equivs e₁/e₂ + charPowerSeries_reindexOp + IH, Finset.prod_subtype + mul_prod_erase; new charPowerSeries_of_isEmpty base) — multinomial fallback NOT needed. [IsTate R] added. BlockOp.lean SORRY-FREE (515→804 lines), std axioms on all key decls) | **File**: PhD/Jacobs/BlockOp.lean | **Depends**: W004, W002, W003, CLEANUP-W1 | **Type**: theorem
- **Decl**: `charPowerSeries_blockDiag`
- **Sketch**: induction on `Finset.univ : Finset σ` / strong induction on card: split
  p := (·.1 = a₀) via W004 (triangular BOTH ways for diagonal ⇒ hypothesis holds);
  left factor = blockCorner a₀ via reindex {x // x.1 = a₀} ≃ I (mathlib equiv:
  search `Equiv.subtypeProd`/build explicit) + W003; right factor = blockOp of the
  restricted σ' := {b // b ≠ a₀} recursion — transport along `{x : σ×I // x.1 ≠ a₀} ≃
  σ' × I` + IH.  Alternatively: direct n-block generalisation of W004's convolution
  (multinomial version) if the induction transport fights — worker's choice, note which.
- **Sources**: [Jac Lemma 1.15] iterated (thesis applies the split twice implicitly).

### [CLEANUP-W2] /cleanup PhD/Jacobs/BlockOp.lean (final)
- **Status**: done (2026-08-05, consolidated closing wave — see AG-W closing note) | **Depends**: W005 | **Type**: cleanup

### [W006] Remaining ε integrality + operators
- **Status**: done — see the completion line below (the stale `open` header was never
  cleared; annotated 2026-09-01).  NOTE: `PhD/Jacobs/` has since been **retired**; the
  left-action tree was superseded by the right-slash fork `PhD/JacobsSlash/` and deleted,
  so this file no longer exists.  Do not pick this ticket up.
- **Superseded header**: | **File**: PhD/Jacobs/DiamondW.lean (deleted) | **Depends**: none (U3Data proved) | **Parallel**: yes (with W001+) | **Type**: theorem+def-holes
- **Decls**: `norm_coeff_h01_le/h10/h20/h21`, the 12 ofGenFun holes of `epsOp01…epsOp21`,
  `isCompactoid_U3MatrixOp` (needs W002 for the last — mark that sub-item dependent)
- **Status**: done (2026-08-05, two workers across the pause; 4 integrality lemmas + hyps_of_norm_coeff/isCompactoid_ofGenFun/isCompactoid_zero_clm helpers + 12 eps-holes + isCompactoid_U3MatrixOp [route (b): 6 per-eps private compactoid lemmas with FULLY EXPLICIT args + nested fin_cases with ONE exact per goal — TRAP DIAGNOSED: `first | exact …` alternation drives the unifier through wrong-branch genFun unification and spins whnf; one-exact-per-goal is cheap, no heartbeat bump needed]. sorryAx debt: only via BlockOp's still-sorried blockOp/isCompactoid_blockOp — clears with W002)
- **Sketch**: integrality: `rowInt_weightGenFun` (public, U3Data) with per-matrix entry
  checks from the ν-table (+ units 2(ν+1), 2(3ν+2), −2ν; a-entries −5(ν−1), 3ν/10, −(ν+2)/10,
  −21ν/2, 7(ν+2)/2, −7(ν−1)/5 — all v = 1 via table + numeral lemmas; c-entries 0 or
  (±)(ν−4)-multiples v ≥ 2; d-units: 2(ν+1), (3ν+2)-forms, −2ν, ν/4 — 1-unit checks
  ‖d−1‖ ≤ ‖3‖: −2ν−1: −2·2695−1 = −5391 = −3·1797 ✓ v ≥ 1; 2ν+2−1 = 2ν+1: 5391 ✓; 6ν+4−1 =
  6ν+3 = 3(2ν+1) ✓; recompute each with norm_num).  Op holes: `hyps_of_row_decay` from the
  integrality (one_mul massage, J015 pattern).  isCompactoid_U3MatrixOp:
  `isCompactoid_blockOp` (W002) + per-block `isCompactoid_of_row_decay`; the 0-blocks:
  IsCompactoid 0 (trivial — small lemma if absent).
- **Sources**: [Jac Lemma 2.7 p. 30] (quote in Tranche A R4).

### [W007] The W operator and `W³ = 1`
- **Status**: done (2026-08-05, worker; toolkit: norm_pow_div_le_one + 5 named specialisations [the exact proof terms inside delta*/Bop/Binvop — W009 rewrites meet them verbatim], diagOp_comp/_eq_id/_comp_eq_id + 4 named telescopes, blockOp_eq_smul_id/_eq_id/smul_inv_ [generic σ, via ext_matrixCoeff], unitPow_delta_cube + κ-reciprocal pairs, delta_cycle_012/120/201. ω-route: linear_combination AVAILABLE, ω³ = 1 := linear_combination (ω−1)*hω, every entry scalar one-shot. NEW TRAP logged: after fin_cases on Fin 3, Matrix.cons_val_* misses the ⟨2,⋯⟩ index — Fin.reduceFinMk must be in the simp only set; and smul_smul normalises to s₃*s₂*s₁ — close scalar goals by linear_combination not rw. Std axioms) | **File**: PhD/Jacobs/DiamondW.lean | **Depends**: W002 (blockOp_comp), W006-holes-pattern | **Type**: theorem
- **Decls**: the 3 δ diagOp-holes, `Wop_cube`
- **Sketch**: holes: ‖(2/5)^n‖ = 1 etc. (numeral lemmas: 2,5,7,10 coprime-3 + norm_inv/
  norm_pow).  Wop_cube: `blockOp_comp` twice ⇒ blockOp of the 3×3 product matrix;
  cyclic × cyclic × cyclic = diagonal with entries δ₀,₁∘δ₁,₂∘δ₂,₀-cyclic-orders; each:
  scalars 4·4·(1/16)·κ(−1/2)²κ(4) with `unitPow_mul` twice [(−1/2)(−1/2) = 1/4 ‖1/4−1‖ =
  ‖3‖ ✓ then (1/4)·4 = 1, `unitPow_one`] = 1; diagOps compose entrywise
  ((2/5)(10/7)(7/4))^n = 1 (`field_simp`/`ring` + `one_pow`); assemble to id via
  matrixCoeff-ext (W002's generic ext) + a small `blockOp`-of-identity-diagonal lemma
  (private).  Sum-collapse: the cyclic products have exactly one nonzero term per entry
  (`Fin.sum_univ_three` + `if`-simp).
- **Sources**: [Jac Remark 2.8.2] (quote in decomposition); erratum 7 note.

### [CLEANUP-W3] /cleanup PhD/Jacobs/DiamondW.lean (cadence after 3rd)
- **Status**: done (2026-08-05, consolidated closing wave — see AG-W closing note) | **Depends**: W006, W007 | **Type**: cleanup

### [W008] B, B⁻¹ and their inverse relations
- **Status**: done (2026-08-05, same worker; 12 holes + Binvop_comp_Bop + AUTHORISED ADDITION Bop_comp_Binvop (statement logged on ticket, same section vars) — diagonal κ(1/4)κ(4) = κ(−1/2)κ(−2) = 1 with Σω-powers = 3, off-diagonal k(1+ω+ω²) = 0; trap-compliant throughout. Exactly 2 sorries remain in the tranche: lemma210 + charPowerSeries_U3MatrixOp) | **File**: PhD/Jacobs/DiamondW.lean | **Depends**: W002, CLEANUP-W3 | **Type**: theorem
- **Decls**: the 12 B/Binv diagOp-holes, `Binvop_comp_Bop`, PLUS (authorised skeleton
  amendment, add the statement): `Bop_comp_Binvop : (Bop …).comp (Binvop …) = id` —
  needed by W011's trace-property step; log the addition.
- **Sketch**: holes as W007's.  Compositions: `blockOp_comp` + smul-bookkeeping
  ((3⁻¹ • blockOp M).comp (blockOp N) = 3⁻¹ • blockOp (M∘N-matrix)); entry (a,c):
  Σ_b over three terms; diagonal: 3⁻¹·(1+1+1)·[κ(4)κ(1/4)/16·16 · D(7/4)D(4/7) etc.] —
  κ-reciprocals via `unitPow_mul` [(1/4)·4 = 1, (−2)(−1/2) = 1; discs: ‖1/4−1‖ = ‖3‖,
  ‖−2−1‖ = ‖3‖, ‖−1/2−1‖ = ‖3‖ ✓] + diagOp-telescopes; off-diagonal: common factor ×
  (1 + ω + ω²) = 0 [linear_combination hω / ring_nf then hω] — per decomposition W8's
  hand-checked (1,2)-case pattern.  Both orders (the ω-power patterns transpose;
  same identities).
- **Sources**: [Jac p. 33] ("moreover, B is invertible", 3B⁻¹ display; quote in
  decomposition).

### [W009] **[Jacobs, Lemma 2.10]**: block-diagonalisation
- **Status**: done (2026-08-05, worker ε; ORCHESTRATOR-VERIFIED. Route: blockOp_comp ×2 + matrixCoeff_blockOp ⇒ 9 scalar goals; single private `entry_master` engine + 4 coefficient-form Lemma 2.11 corollaries [signatures on ε's report: coeff_lemma211_first/first'/second/second'] + 2 new κ-products [κ(−2)κ(1/4) = κ(−1/2), κ(4)κ(−1/2) = κ(−2)]; each entry ONE linear_combination; B/B⁻¹ transcription correct FIRST TRY [errata 6–7 held]. Scalar patterns: entry = 3⁻¹[(χ+θ+ψφ)T₁ + (ψ+φ+χθ)T₂]; ω³ = 1 never needed. FINDING for cleanup: hν2 UNUSED in lemma210 — drop authorised, see CLEANUP wave) | **File**: PhD/Jacobs/DiamondW.lean | **Depends**: W006, W008 | **Type**: theorem (LARGE)
- **Decl**: `lemma210`
- **Sketch**: `blockOp_comp` twice ⇒ entrywise identity of 3×3 operator matrices; each
  entry (a,c) = 3⁻¹ Σ_{b,b'} Binv_{ab} ∘ ε_{b,b'} ∘ B_{b'c} (six nonzero terms — zero
  ε-diagonal).  Translate each `D(α)∘ε∘D(β)` composite to generating-function language
  (`matrixCoeff_diagOp_comp` (GenFun) + `matrixCoeff_ofGenFun` + `coeff_diagRescale`)
  and apply THE PROVED Lemma 2.11 identities (lemma211_first/first'/second/second',
  U3Data) to pair terms; collect ω-scalars; diagonal entries assemble to
  M11/M22/M33genFun (definition match), off-diagonal cancel via (1 + ω + ω²) = 0 —
  the thesis: "all the cancellation is evident" from 2.11 (quote in decomposition).
  Close entries by matrixCoeff-ext.  IF an entry refuses: re-check B-transcription
  (errata 6–7) and the ω-bookkeeping BEFORE anything else; then hard-stop with the
  failing entry.
- **Sources**: [Jac Lemma 2.10 (2.1.14) pp. 33–34 + Lemma 2.11 proof note] (quotes in
  decomposition).

### [W010] M₁,₁ / M₃,₃ operator holes
- **Status**: done — see the completion line below (the stale `open` header was never
  cleared; annotated 2026-09-01).  NOTE: `PhD/Jacobs/` has since been **retired**; the
  left-action tree was superseded by the right-slash fork `PhD/JacobsSlash/` and deleted,
  so this file no longer exists.  Do not pick this ticket up.
- **Superseded header**: | **File**: PhD/Jacobs/DiamondW.lean (deleted) | **Depends**: none (uses U3Data) | **Parallel**: yes | **Type**: lemma-holes
- **Status**: done (2026-08-05; norm_coeff_M11genFun_le [no ω] + norm_coeff_M33genFun_le [norm_omega hω] + 4 holes; M33op AMENDMENT EXECUTED as authorised: signature now (ω) (_hω : ω^2+ω+1=0) (_h3) (_ht) (_hνc), call sites in lemma210/charPowerSeries_U3MatrixOp updated to `M33op ω hω h3 ht hνc` — both eigenblock ops now share M22op's shape; std axioms)
- **Sketch**: integrality bounds for M11genFun/M33genFun = the `norm_coeff_M22genFun_le`
  proof with scalars 1/ω/ω² (‖ω‖-free for M11; M33 needs ‖ω‖ ≤ 1 — NOTE: M33op carries
  NO hω! Its holes need ‖ω^k‖ ≤ 1 — CHECK whether provable without hω... NOT provable
  for wild ω (the M22-B2 family AGAIN, anticipated this time): the M33op def's holes are
  UNPROVABLE as the def stands.  AUTHORISED FIX (same-day design decision, do it at
  pickup): add `(_hω : ω ^ 2 + ω + 1 = 0)` to M33op's signature + update lemma210/
  charPowerSeries_U3MatrixOp call sites (`M33op ω _hω h3 ht hνc`); log as skeleton
  amendment; b2_log entry NOT needed (caught at planning, recorded here).
- **Sources**: [Jac (2.1.14), §2.2 p. 40].

### [CLEANUP-W4] /cleanup PhD/Jacobs/DiamondW.lean (cadence)
- **Status**: done (2026-08-05, consolidated closing wave — see AG-W closing note) | **Depends**: W008, W009, W010 | **Type**: cleanup

### [W011] **MILESTONE**: `det(1 − T·U₃) = ∏ det(1 − T·M_{t,t})`
- **Status**: done (2026-08-05, worker ε; ORCHESTRATOR-VERIFIED std axioms [propext, Classical.choice, Quot.sound] on both endpoints; comp_left orientation = (isCompactoid_U3MatrixOp).comp_left Binvop; trace property + Bop_comp_Binvop + lemma210 + charPowerSeries_blockDiag + blockCorner_blockOp + Fin.prod_univ_three. PROJECT-WIDE 0 SORRIES in the 9 core PhD.Jacobs modules; DiamondW 1270 lines) | **File**: PhD/Jacobs/DiamondW.lean | **Depends**: W005, W006, W008, W009, W010, CLEANUP-W4 | **Type**: theorem (milestone)
- **Decl**: `charPowerSeries_U3MatrixOp`
- **Sketch**: trace property (`TateFredholm.charPowerSeries_comm`): u := Binvop ∘
  U3MatrixOp (compactoid: `IsCompactoid.comp_left`-family (TateFredholm Matrix.lean:492/533
  — check orientation) from `isCompactoid_U3MatrixOp`), v := Bop; u∘v = B⁻¹AB (assoc),
  v∘u = Bop∘Binvop∘A = A (`Bop_comp_Binvop` from W008 + comp-assoc + id-comp) ⇒
  charPS(A) = charPS(B⁻¹AB); rewrite `lemma210`; `charPowerSeries_blockDiag` (W005)
  [diagonality hypothesis from `matrixCoeff_blockOp` + off-diagonal-zero blocks:
  matrixCoeff of 0-op = 0 — small lemma]; `blockCorner_blockOp` lands the three factors;
  `Fin.prod_univ_three` shapes the product.  Run `#print axioms` (standard three).
- **Sources**: [Jac Lemma 1.15 + pp. 32–34]; assembles Tranche A (M₂,₂) and feeds AG-EXT
  (M₃,₃).

### [CLEANUP-W-FINAL] /cleanup-all over PhD/Jacobs (post-milestone)
- **Status**: done (2026-08-05, consolidated closing wave — see AG-W closing note) | **Depends**: W011 | **Type**: cleanup


## AG-W TRANCHE COMPLETE (2026-08-05)
All 11 proof tickets + cleanups done. BlockOp.lean (804 l.) + DiamondW.lean (~1270 l.):
0 sorries, 0 warnings, milestone endpoints `lemma210` and `charPowerSeries_U3MatrixOp`
on exactly [propext, Classical.choice, Quot.sound] (orchestrator-verified twice).
AUTHORISED AMENDMENT executed at cleanup: hν2 dropped from both endpoints (unused —
extends the Tranche-A minimality finding; zero external call sites).  Result chain:
`det(1 − T·U₃matrix) = det(1−T·M₁,₁)·det(1−T·M₂,₂)·det(1−T·M₃,₃)` via Serre's partition
lemma (charPowerSeries_partition/blockDiag, TateFredholm generality, [IsTate R] per the
machine-checked B2), Lemma 2.10 (nine one-line linear_combination entries over the
Lemma 2.11 coefficient corollaries), W³ = 1, both B-inverse relations.  Two thesis
errata (6–7) recorded.  PUBLIC-API/UPSTREAMING candidates noted in the cleanup report
(finsetSplit, charPowerSeries_of_isEmpty, minor factorisation lemmas → TateFredholm;
diagOp_comp family → GenFun; blockOp-calculus → BlockOp proper).
LEDGER: Tranche A + AG-NP + AG-W proved.  AG-EXT ready (M33op + integrality live).
AG-B: skeleton at PhD/Jacobs/U3/ (8 files) exists from a parallel session with the
user's deferred/scheduled decision in Hurwitz.lean — ticketing awaits user direction.
