# Ticket Board — lwx-halo (LWX Theorem 3.16 + Corollary 3.18, Tier 1)

**BOARD PATH: `.mathlib-quality/lwx-halo/`** — name it in every `/beastmode`
invocation. The default `.mathlib-quality/` root is the (completed) NewtonPolygons
board; `qmf/`, `jacobs/`, `slopes-hecke/`, … are other projects' property — never touch
any of them.

**Skeleton is canonical.** Every ticket = "fill the named `sorry`s in the named file";
all statements already exist and `lake build PhD.TateFredholm.TwoSidedBound PhD.LWX.Halo
PhD.LWX.IntegralModel` is green (0 errors, sorries only; re-verified 2026-09-03 after
the tranche-H revision). Statements are ticket-protected; the ONLY sanctioned statement
edit is the C4 VERIFY-spot (hypotheses of `nat_ineq_3_13_2` — see the ticket). Read `decomposition.md` (this directory) for
per-leaf source quotes, Lean ↔ source match paragraphs, and attack logs BEFORE starting
a ticket; `plan.md` for the architecture (D′) and the deferred seams.

Governing principles (inherited house rules): no duplicate code; every deletion/rename
→ `.mathlib-quality/renames.jsonl`; `lia` → `omega`; never touch `PhD/PR'd/`; another
agent may build this repo concurrently — never kill a running `lake build`.

Source: **[LWX]** = Liu–Wan–Xiao, arXiv:1412.2584v4 (PDF with the user; page numbers =
printed pages). Scope: `p` odd, per-ω, `UpDatum`-abstract; out-of-scope items in
plan.md.

## Summary — **BOARD COMPLETE 2026-09-04**
- Total: 30 proof/def tickets + 14 cleanup = 44 — **ALL DONE**
- Open: 0 | In Progress: 0 | Done: 44
- Milestones, all sorry-free on standard axioms (propext/Classical.choice/Quot.sound):
  - **F2** ([LWX] Theorem 3.16): `norm_charCoeff_upOp_le`,
    `exists_charCoeff_upOp_eq_T_pow_mul`, `norm_coeff_charCoeff_upOp_le` (Halo.lean)
  - **F3** ([LWX] Corollary 3.18): `isBelow_newtonPolygon_specCharSeries` (Halo.lean)
  - **H5** (the seam): `intEvalAtReps_comm` (IntegralModel.lean) — any `Φ` on
    `S^D_int` satisfying the [LWX, Prop 3.1] display intertwines with `UpDatum.op`,
    so Theorem 3.16 / Corollary 3.18 apply to the genuine `[UηU]`
- Statement fixes en route (b2_log.jsonl + renames.jsonl): C3 (added `[CharZero L]`
  + `ρ ≤ 1`), H4/H5 (T-rescaled transport not c₀ — restated in the plain Mahler
  basis: `cfunSlash_mahlerON` / `mahlerON_seqSlash` / plain `seqSlash_coeff`)
- Bonus infrastructure: `Algebra ℤ_[p] (HaloInt p)` + `IsBoundedSMul` (HaloRing.lean)
  make `Λ^{>1/p}` an ultrametric `ℤ_p`-Banach algebra, unlocking mathlib's
  `PadicInt.mahlerSeries`/`hasSum_mahler`/`fwdDiff_tendsto_zero` wholesale;
  `PadicExpLog.lean` (p-generic exp/log, ported from Jacobs p=3);
  `UpDatum.op_apply` (UpMatrix.lean)
- runLinter clean on all board files (HaloRing, PadicExpLog, UnitsLog, TiltedDegree,
  UpMatrix, Halo, IntegralModel, TateFredholm/TwoSidedBound); `lake build` green
  (2587 jobs)
- Deferred (NOT this board): FUTURE-JacobsExpLog (refactor Jacobs onto PadicExpLog);
  future boards `lwx-slopes` / `tate-riesz`; `M₁` ≃ `QMF.Sigma0'` polish

## Dependency fronts
```
A1 → A2 → A3 → CLEANUP-1 → A4 → A5 → CLEANUP-2 ─────────────┐
B1 ; B2 → B3 → CLEANUP-3 ──────────────┐                     │
C1 → C2 ─┐                             │                     │
C3 ──────┼→ C5 → C6 → CLEANUP-5        │                     │
C4 ──────┘   (CLEANUP-4 after C3)      │                     │
D1 → D2 (needs B) → D3 (needs A4,C5,C6) → CLEANUP-6 → D4 → CLEANUP-7
E1 → E2 ; E3 → CLEANUP-8                                     │
F1 ; G1                                                      │
all of A4,D4,E2,E3,F1 → CLEANUP-ALL-1 → F2 → CLEANUP-9 → F3 → CLEANUP-10 → CLEANUP-FINAL
H1 (needs A1,B1,B3) → H2 (needs D1) → H3 (needs A4) → CLEANUP-H1
  → H4 (needs D3) → H5 (needs D4, CLEANUP-ALL-1) → CLEANUP-H2 → CLEANUP-FINAL
```

---

## Tranche A — the ring `Λ^{>1/p}` (`PhD/LWX/HaloRing.lean`)

### [A1] The convolution ring: carrier bounds + `CommRing` fields
- **Status**: done (finished 2026-09-03T10:03Z) | **File**: PhD/LWX/HaloRing.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T10:03Z: DONE — all A1 sorries filled: bound fields (Zero/One/Add/Neg/Mul),
    `summable_mul_coeff` via new private `tendsto_cofinite_of_three_bounds` (the
    three-exponent cofinite-decay workhorse, reused for assoc), `norm_mul_coeff_le`,
    `norm_mul₃_le`, `assocEquiv` (= prodShear ∘ prodComm, no bespoke Equiv proofs),
    `summable_assoc_left/right`, and all CommRing fields.  `mul_assoc` went exactly per
    sketch: tsum_mul_right/left, `Summable.tsum_prod'` (NB: this mathlib's tsum_prod'
    takes a per-fiber summability argument h₁ — supplied via .mul_left/.mul_right),
    `assocEquiv.tsum_eq`, termwise `mul_assoc + ring_nf`.  `mul_comm` via
    `Equiv.subLeft k`.  lake build clean.  Phase 6.5 note: full /cleanup deferred to
    CLEANUP-1 per board cadence design (file-level cleanup after A3).
- **Parallel**: yes | **Type**: def + lemma (the board's largest single ticket)
- **Statement**: fill the `sorry`s in the `Zero/One/Add/Neg/Mul` instance bound fields,
  `summable_mul_coeff`, and the `CommRing` proof fields (HaloRing.lean:66–128).
- **Proof sketch**:
  1. Bound fields: additive ones by ultrametric triangle (`norm_add_le` + `max` of the
     two bounds); `one`/`zero` by case split; `mul` bound: each term has
     `v(f_i·g_{k−i}) ≥ max(0,−i) + max(0,i−k) ≥ max(0,−k)`, then
     `TateFredholm.norm_tsum_le_iSup`.
  2. `summable_mul_coeff`: `TateFredholm.summable_of_tendsto_cofinite`; cofinite decay
     since for `|i|` large one factor's bound `p^{min(0,i)}`/`p^{min(0,k−i)}` is small.
  3. Additive axioms: `ext` + coefficientwise (`coeff_add` etc. are `rfl`).
  4. `mul_comm`: reindex the tsum by the involution `i ↦ k − i`
     (`Equiv.subLeft k`, `Equiv.tsum_eq`) + `mul_comm` in `ℤ_[p]`.
  5. `one_mul`/`mul_one`: the tsum collapses at the delta (`tsum_eq_single`).
  6. Distributivity: `tsum_add` with the two summabilities from step 2.
  7. `mul_assoc` (the hard one): both sides are the double tsum
     `∑'_{(i,j)} f_i g_j h_{k−i−j}` — prove each equal to it via
     `tsum_mul_right`-pushing, `Summable.tsum_prod`/`tsum_comm'` Fubini justified by
     norm-summability on `ℤ×ℤ` (all weighted norms ≤ 1 and cofinitely small; see
     decomposition A1 attack log), or via `HasSum` characterisations
     (`HasSum.mul_eq`-style with `tsum_mul_tsum_of_summable_norm`).
- **Mathlib lemmas needed**: `TateFredholm.summable_of_tendsto_cofinite`,
  `TateFredholm.norm_tsum_le_iSup` (project, Tate.lean); `tsum_eq_single`,
  `Equiv.tsum_eq`, `tsum_add`, `Summable.tsum_prod'`, `tsum_comm'`,
  `tsum_mul_tsum_of_summable_norm`, `summable_mul_of_summable_norm`
  (Analysis/Normed/Ring/InfiniteSum), `IsUltrametricDist.norm_add_le_max`.
- **Sources**: [LWX, Lemma 3.15] p. 21 + [LWX, Cor 3.18 proof] p. 23;
  decomposition.md A1.
- **Generality decision**: fixed odd-`p` carrier over `ℤ_[p]` (per-ω per plan.md);
  no `Algebra` structure yet (add only if a later ticket needs it).

### [A2] The norm layer
- **Status**: done (finished 2026-09-03T10:35Z) | **File**: PhD/LWX/HaloRing.lean | **Depends on**: A1
- **Progress**:
  - 2026-09-03T10:35Z: DONE — route change (recorded per 4e): the hand-rolled NormedRing field
    stack fought defeq, so the norm layer is built the mathlib way: private `gnorm`
    primitives (`gterm_le_one/_nonneg`, `bddAbove`, `le_iff`, `zero`,
    `eq_zero_of_gnorm_eq_zero`, `gnorm_add_le_max`, `gnorm_neg`,
    `norm_coeff_le_gnorm_mul`, `gnorm_mul_le`), bundled as an `AddGroupNorm` →
    `AddGroupNorm.toNormedAddCommGroup`, then `NormedRing`/`NormedCommRing` by
    structure-merge, `NormOneClass`, `IsUltrametricDist` (via `dist_eq_norm` +
    `gnorm_add_le_max`), `norm_le_one`, `norm_coeff_le_norm`, `norm_le_zpow_iff`
    (via `le_div_iff₀` + `zpow_sub₀`).  Same statements, same math; norm still
    definitionally `⨆ j, ‖f j‖·p^{−j}` (`norm_def := rfl`).  lake build clean.
    Cleanup deferred to CLEANUP-1 per cadence.
- **Parallel**: after A1 | **Type**: instance + lemma
- **Statement**: `NormedRing` proof fields (dist axioms, `dist_eq`, `norm_mul_le`),
  `NormOneClass`, `IsUltrametricDist`, `norm_le_one`, `norm_coeff_le_norm`,
  `norm_le_zpow_iff` (HaloRing.lean:130–170).
- **Proof sketch**: the norm is `⨆ j, ‖f j‖·p^{−j}`, a sup of a family in `[0,1]`
  (bounded: the bound field). (1) `Real.iSup` API (`Real.iSup_le`, `le_ciSup` with
  `BddAbove`) for all comparisons; (2) `dist_eq` is `rfl`-adjacent by design;
  (3) `norm_mul_le`: termwise `‖(fg)_k‖p^{−k} ≤ sup_i (‖f_i‖p^{−i})(‖g_{k−i}‖p^{−(k−i)})
  ≤ ‖f‖‖g‖` via `norm_tsum_le_iSup`; (4) ultrametric: sup of ultrametric families;
  (5) `norm_le_zpow_iff`: unfold the sup; `‖f j‖p^{−j} ≤ p^{−k} ↔ ‖f j‖ ≤ p^{j−k}`
  (`zpow` arithmetic, `p > 1` from `hp.out.one_lt`).
- **Mathlib lemmas needed**: `Real.iSup_le`, `le_ciSup`, `ciSup_le_iff`,
  `zpow_le_zpow_right_of_le_one`-family, `one_lt_cast`.
- **Sources**: [LWX, Lemma 3.15]; decomposition.md A2.
- **Generality decision**: `‖T‖ = p⁻¹` normalisation (const isometric); documented in
  the file docstring.

### [A3] Completeness
- **Status**: done (finished 2026-09-03T10:38Z) | **File**: PhD/LWX/HaloRing.lean | **Depends on**: A2
- **Progress**:
  - 2026-09-03T10:38Z: DONE — `CompleteSpace (HaloInt p)` via `Metric.complete_of_cauchySeq_tendsto`:
    coefficient maps are `p^j`-Lipschitz (`Real.toNNReal` constant), coefficientwise
    limits in complete `ℤ_[p]`, the halo bound is closed (`le_of_tendsto`), and the
    gauge convergence per coefficient via `le_of_tendsto` on the Cauchy tail +
    `ciSup_le`.  New helper `norm_coeff_le_norm_mul` (the `‖f j‖ ≤ ‖f‖·p^j` reading).
    lake build clean.
- **Parallel**: no | **Type**: instance
- **Statement**: `CompleteSpace (HaloInt p)` (HaloRing.lean:~168).
- **Proof sketch**: a Cauchy sequence is coefficientwise Cauchy (each
  `f ↦ f j` is `p^{j}`-Lipschitz for the gauge by `norm_coeff_le_norm`); limits
  `d_j := lim fₙ j` exist in `ℤ_[p]` (complete), satisfy the bound field (closed
  condition), and `fₙ → d` in gauge norm by uniformity of the Cauchy modulus
  (standard `cauchySeq_tendsto_of_complete` massage; mirror the pattern of
  `TateFredholm/OperatorNorm.lean`'s completeness proof).
- **Mathlib lemmas needed**: `Metric.complete_of_cauchySeq_tendsto`,
  `Filter.Tendsto` glue; `PadicInt.instCompleteSpace`.
- **Sources**: decomposition.md A3. | **Generality**: n/a.

### [CLEANUP-1] /cleanup on PhD/LWX/HaloRing.lean (cadence)
- **Status**: done (finished 2026-09-03T10:38Z) | **Depends on**: A3 | **Blocks**: A4, A5 | **Type**: cleanup
- **Progress**:
  - 2026-09-03T10:38Z: inline cadence cleanup of the A1–A3 region (full-file /cleanup deferred to
    CLEANUP-2 when the file is sorry-free — a mid-file /cleanup would trip on the
    A4/A5 skeleton sorries): deduped `norm_coeff_le_norm_mul` (kept the pre-instance
    `norm_coeff_le_gnorm_mul`, single spelling), deleted unused `gnorm_le_iff`,
    deprecation fix (`Set.mem_ofPred_eq`).  `lake exe runLinter PhD.LWX.HaloRing`:
    zero hits on this file (one pre-existing unusedArguments hit in
    TateFredholm/Tate.lean, out of board scope — noted for that file's owners).

### [A4] `T` and `T^k`-divisibility API (+ `const`)
- **Status**: done (finished 2026-09-03T10:40Z) | **File**: PhD/LWX/HaloRing.lean | **Depends on**: CLEANUP-1
- **Progress**:
  - 2026-09-03T10:40Z: DONE — `T` bound field, `coeff_T_mul` (tsum_eq_single 1), NEW public
    `coeff_T_pow_mul` (k-fold shift, induction via `pow_succ'` — natural API the F2/H4
    consumers will want), `norm_T_mul` (le_antisymm, both directions by `ciSup_le` +
    shift; `Real.mul_iSup_of_nonneg` for the constant), `exists_T_pow_mul_of_norm_le`
    (witness = the shifted stream, bound field split on `0 ≤ j` via `norm_le_zpow_iff`),
    `norm_le_of_eq_T_pow_mul`, `const` + `coeff_const` + `norm_const` + `const_mul`.
    lake build clean.
- **Parallel**: with A5 after CLEANUP-1 | **Type**: lemma
- **Statement**: `T` bound field, `coeff_T_mul`, `norm_T_mul`,
  `exists_T_pow_mul_of_norm_le`, `norm_le_of_eq_T_pow_mul`, `const` bound field,
  `norm_const`, `const_mul` (HaloRing.lean:141–186).
- **Proof sketch**: (1) `coeff_T_mul`: the convolution against a delta collapses
  (`tsum_eq_single 1`); (2) `norm_T_mul`: reindex the sup by `j ↦ j+1`
  (`Equiv.addRight`), pulling out one factor `p⁻¹`; (3) `T^k` versions by induction;
  (4) `exists_T_pow_mul_of_norm_le`: candidate `g := shift_{−k} f`; its bound field is
  exactly `norm_le_zpow_iff`'s content (A2); equality by `ext` + iterated
  `coeff_T_mul`; (5) `const_mul`: delta convolution.
- **Mathlib lemmas needed**: `tsum_eq_single`, `Equiv.iSup_congr`-style reindexing.
- **Sources**: [LWX, Lemma 3.15 proof] ("`p = pT⁻¹ · T`"); decomposition.md A4.
- **Generality**: statements in `zpow`-of-real form; no ideal-power API (plan.md).

### [A5] Specialization at a halo point
- **Status**: done (finished 2026-09-03T10:46Z) | **File**: PhD/LWX/HaloRing.lean | **Depends on**: CLEANUP-1
- **Progress**:
  - 2026-09-03T10:46Z: DONE — new private helpers `norm_spec_term` (isometric ψ + `norm_zpow`),
    `one_lt_p_mul` (`1 < p·‖T₀‖`), `tendsto_spec_cofinite` (bad set inside
    `Icc (−M₂) M₁`: right tail by `‖T₀‖^j`, left tail by `(p‖T₀‖)^j`);
    `summable_specialize`; `norm_specialize_le` = LWX (3.18.1) verbatim (two branches:
    `j ≥ k` trivial-integral, `j < k` via `1 ≤ (p‖T₀‖)^{k−j}` + `inv_le_iff_one_le_mul₀`);
    `specialize_one`.  **TRANCHE A COMPLETE: HaloRing.lean is sorry-free, 0 errors,
    axioms standard three on headliners, runLinter zero hits.**
- **Parallel**: with A4 | **Type**: def + lemma
- **Statement**: `summable_specialize`, `norm_specialize_le`, `specialize_one`
  (HaloRing.lean:188–204).
- **Proof sketch**: (1) summability: termwise `‖ψ(f j)T₀^j‖ = ‖f j‖·‖T₀‖^j`; right
  tail `≤ ‖T₀‖^j → 0`; left tail `≤ (p·‖T₀‖…)`: `‖f j‖ ≤ p^{j}` for `j < 0` gives
  `‖f j‖‖T₀‖^j ≤ (p‖T₀‖)^{j} → 0` as `j → −∞` since `p‖T₀‖ > 1`; conclude with
  `summable_of_tendsto_cofinite`. (2) `norm_specialize_le` ([LWX, (3.18.1)]):
  `norm_tsum_le_iSup`, then per `j`: if `j ≥ k` use `‖T₀‖^j ≤ ‖T₀‖^k`; if `j < k` use
  `‖f j‖ ≤ p^{j−k}` (from `norm_le_zpow_iff`) and `p^{j−k} ≤ ‖T₀‖^{k−j}·…` — the
  two-branch computation in decomposition.md A13, driven by `p⁻¹ < ‖T₀‖ < 1`.
  (3) `specialize_one`: `tsum_eq_single 0`.
- **Mathlib lemmas needed**: `zpow_le_zpow` family for base in `(0,1)`;
  `TateFredholm.norm_tsum_le_iSup`; `summable_of_tendsto_cofinite`.
- **Sources**: [LWX, Cor 3.18] p. 23, display (3.18.1); decomposition.md A13.
- **Generality**: `K` any complete ultrametric `NontriviallyNormedField` + isometric
  `ψ` — strictly more general than `ℂ_p`.

### [CLEANUP-2] /cleanup on PhD/LWX/HaloRing.lean (final)
- **Status**: done (finished 2026-09-03T10:46Z) | **Depends on**: A4, A5 | **Type**: cleanup
- **Progress**:
  - 2026-09-03T10:46Z: inline final pass: file sorry-free; `lake exe runLinter` zero hits on the
    file; `#print axioms` standard three on `norm_specialize_le`,
    `exists_T_pow_mul_of_norm_le`, `instCommRing`; unusedSectionVars omits added;
    deprecations fixed.  The full 10-phase `/cleanup` skill run is consolidated into
    CLEANUP-ALL-1 (pre-milestone) — recorded so the audit trail shows the deferral.

---

## Tranche B — Teichmüller and `qlog` (`PhD/LWX/UnitsLog.lean`)

### [B1] Teichmüller lift
- **Status**: done (finished 2026-09-04T10:20Z) | **File**: PhD/LWX/UnitsLog.lean | **Depends on**: none
- **Progress**:
  - 2026-09-04T10:20Z: DONE per sketch.  Fermat: `ZMod.pow_card` through `PadicInt.toZMod` +
    `ker_toZMod` + `maximalIdeal_eq_span_p`; consecutive bound via
    `dvd_sub_pow_of_dvd_sub` (import `Mathlib.NumberTheory.Basic`; apply it DIRECTLY
    at `R := ℤ_[p]` — exact_mod_cast mangles the `(p ^ (k+1) : R)` cast) +
    `norm_le_pow_iff_mem_span_pow`; Cauchy via
    `SeminormedAddCommGroup.cauchySeq_of_le_geometric` (`C = r = p⁻¹`, import
    `Analysis.SpecificLimits.Normed`); `teichAux := limUnder atTop` +
    `CauchySeq.tendsto_limUnder`; unit structure by exhibiting the inverse limit
    (`Units.mk` with `teichAux ↑x⁻¹` — no norm-1 argument needed); mod-`p` congruence
    by ultrametric telescoping + `le_of_tendsto`, and the final bound via
    `x·ωT(x)⁻¹ − 1 = (x − ωT(x))·(inverse value)`.
- **Parallel**: yes | **Type**: def + lemma
- **Statement**: `teichmuller` (def-hole: `lim_{n} x^{pⁿ}`), `teichmuller_mul`,
  `norm_mul_teichmuller_inv_sub_one_le` (UnitsLog.lean:38–52).
- **Proof sketch**: (1) `‖x^{p^{n+1}} − x^{pⁿ}‖ ≤ p^{−(n+1)}`: from
  `a^p ≡ a [p·(a − b …)]`-style congruence (`sub_dvd`-binomial expansion; mathlib:
  `Int.ModEq`-analogue on `ℤ_[p]` via `PadicInt.norm_le_pow_iff_mem_span_pow` and
  `dvd_sub_pow_of_dvd_sub`); (2) Cauchy ⟹ limit (`CompleteSpace ℤ_[p]`); define on
  units, value a unit (norm-1 limit); (3) multiplicativity: limits of products;
  (4) `x^{pⁿ} ≡ x [p]` by Fermat (`ZMod.pow_card`-transport through `toZMod`), pass to
  the limit.
- **Mathlib lemmas needed**: `dvd_sub_pow_of_dvd_sub` (verify name at start; it
  exists for commutative rings), `PadicInt.norm_le_pow_iff_mem_span_pow`,
  `PadicInt.toZMod`, `ZMod.pow_card`.
- **Sources**: [LWX, Notation 2.1]; decomposition.md B1 (AG1).
- **Generality**: stated for all primes (limit exists; only the *splitting* use is
  odd-`p`).

### [B2] `qlog`: convergence and integral margin
- **Status**: done (finished 2026-09-04T10:45Z) | **File**: PhD/LWX/UnitsLog.lean | **Depends on**: none
- **Progress**:
  - 2026-09-04T10:45Z: DONE.  Single shared termwise bound `norm_qlog_term_le`:
    `‖term k‖ ≤ ‖u−1‖·(k+1)·p^{−k}` (`Nat.ordProj_le` + `factorization_def` for
    `p^{v(k+1)} ≤ k+1`); summability via `TateFredholm.summable_of_tendsto_cofinite`
    (import `PhD.TateFredholm.Tate`; `Nat.cofinite_eq_atTop` + `squeeze_zero_norm`,
    decay from `summable_pow_mul_geometric_of_norm_lt_one 1` + geometric, summed);
    `norm_qlog_le` via `TateFredholm.norm_tsum_le_iSup` + `Real.iSup_le` +
    `(k+1) ≤ p^k` (`Nat.lt_pow_self`).  `hp2` unused (the ≤-form needs no odd-`p`
    margin) — binder underscore-prefixed, statement otherwise verbatim.
- **Parallel**: yes | **Type**: lemma
- **Statement**: `summable_qlog`, `norm_qlog_le` (UnitsLog.lean:66–77).
- **Proof sketch**: termwise `v((u−1)^{k+1}/(k+1)) ≥ (k+1)·v(u−1) − v(k+1)
  ≥ v(u−1) + (k − v(k+1)) ≥ v(u−1)` at odd `p` (`v(k+1) ≤ log_p(k+1) ≤ k`); decay to
  `∞` gives summability; `norm_tsum_le_iSup` gives the bound with the `k = 0` term
  dominating.
- **Mathlib lemmas needed**: `padicValNat`-vs-`log` bound (`padicValNat_le_nat_log`
  or `Nat.lt_pow_self`-route), `norm_div`, `Padic.norm_intCast`-family,
  `TateFredholm.norm_tsum_le_iSup`.
- **Sources**: [LWX, Notation 2.1]; decomposition.md B2.
- **Generality**: `p ≠ 2` only where the margin needs it (as stated).

### [B3] `qlog` additivity + the log shape
- **Status**: done (finished 2026-09-04T12:10Z) | **File**: PhD/LWX/UnitsLog.lean | **Depends on**: B2
- **Progress**:
  - 2026-09-04T12:10Z: DONE via the sanctioned mirror route: NEW FILE `PhD/LWX/PadicExpLog.lean`
    (~830 lines) — the `p`-generic port of JacobsSlash/1_PadicAnalytic.lean's `p = 3`
    exp/log theory over ultrametric `K` with `‖p‖ < 1` (docstrings all `p`-general).
    Genuinely new mathematics in the port: `norm_pow_p_sub_one`
    (`‖uᵖ−1‖ = ‖p‖‖u−1‖`) replaces the `p = 3` cube-factorisation with
    `geom_sum_mul` + the double sum `T − p = (u−1)·S`, `S ≡ ∑_{i<p} i mod (u−1)`,
    and `p ∣ ∑_{i<p} i` for ODD `p` (where `p ≠ 2` genuinely enters);
    `padicExp_natCast_mul` (`exp(n·w) = exp(w)ⁿ`) replaces the `3 = 1+2` splitting.
    `p ≠ 2` also threads through `4v ≤ pᵛ+3` and the Legendre margin
    `2v_p(n!) ≤ n−1`.  Headline: `PadicExpLog.padicLog_mul`.
    In UnitsLog: `qlog` REDEFINED as `padicLog ∘ (↑)` (user-directed dedup, recorded
    in renames.jsonl; old series formula = `qlog_eq_tsum`); `qlog_mul`,
    `isLogShape_qlogLinearCoeff` (norm-cancellation arithmetic),
    `hasSum_qlogLinearCoeff` (series `HasSum` + `hasSum_nat_add_iff' 1` reindex —
    apply the iff via `refine ... .mp ?_`, standalone `have` can't infer the
    implicits), `IsLogShape.add_const` (beta-`show` before the ite-rewrites).
    runLinter clean on both files; all standard axioms.
    FUTURE ticket [FUTURE-JacobsExpLog] queued to rebase JacobsSlash onto the
    general file.  NOTE runLinter surfaced two PRE-EXISTING TateFredholm/Tate.lean
    findings (PseudoUniformizer.coe_eq syntactic-rfl, norm_inv_mul unused
    NormOneClass) — outside this board; left for a TateFredholm cleanup.
- **Parallel**: after B2 | **Type**: lemma (load-bearing: see decomposition finding 1)
- **Statement**: `qlog_mul`, `isLogShape_qlogLinearCoeff`, `hasSum_qlogLinearCoeff`,
  `IsLogShape.add_const` (UnitsLog.lean:84–101).
- **Proof sketch**: (1) `qlog_mul`: with `x = u−1, y = v−1`,
  `uv − 1 = x + y + xy`; expand `qlog(uv)` and rearrange the double series into
  `qlog u + qlog v` by the classical formal-identity-plus-estimates argument; the
  fork's `PhD/JacobsSlash/1_PadicAnalytic.lean` exp/log lemmas are the working
  pattern (mirror, do not import). Alternative sanctioned route: prove
  `padicExp`-analogue `exp (qlog u) = u` on the domain and transport multiplicativity
  through injectivity of `exp` — worker's choice, record which. (2) shape lemmas:
  one-line valuation arithmetic + `HasSum` of the geometric-type series
  (`hasSum_geometric`-adjacent, or direct via `summable_of_tendsto_cofinite` and
  `tsum` reindex `k ↦ k+1`). (3) `add_const`: case split on `k`.
- **Mathlib lemmas needed**: `tsum` reindexing (`Equiv.tsum_eq` at `Equiv.addRight 1`
  on `ℕ`… use `tsum_eq_zero_add`-family), `Finset.sum_range_choose`-free binomial
  manipulations.
- **Sources**: [LWX, Prop 3.14 proof] p. 21 (the split); decomposition.md B4/B5 and
  planning finding 1.
- **Generality**: domain `1 + pℤ_p`, odd `p`.

### [FUTURE-JacobsExpLog] Refactor JacobsSlash onto the general `PadicExpLog`
- **Status**: MOVED → executed on its own board `.mathlib-quality/jacobs-explog/`
  (R1–R3 done 2026-09-05: 1_PadicAnalytic.lean is now the `p = 3` shim layer +
  §§UnitPow/Binomial; full JacobsSlash tree green with zero downstream edits; see that
  board's tickets.md / renames.jsonl) | **File**: PhD/JacobsSlash/1_PadicAnalytic.lean
  → PhD/LWX/PadicExpLog.lean | **Depends on**: B3 | **Type**: refactor
- **Statement**: `PhD/LWX/PadicExpLog.lean` (created by B3) is the `p`-generic port
  of the `p = 3` exp/log development in `PhD/JacobsSlash/1_PadicAnalytic.lean`
  (same lemma names, `(3 : K)` → `((p : ℕ) : K)`, `padicValNat 3` → `padicValNat p`,
  section hypothesis `‖p‖ < 1`, `p ≠ 2` threaded only through
  `four_mul_padicValNat_three_le`/`sq_norm_factorial_ge` and their consumers).
  Once stable, make JacobsSlash consume it: instantiate at `p := 3`
  (`Fact (Nat.Prime 3)`, `hp2 : (3:ℕ) ≠ 2 := by norm_num`) and delete the
  duplicated §§ResidueChar/NatAux/LogExp of 1_PadicAnalytic.lean, keeping only the
  `p = 3`-specific `UnitPow`/`binomialCoeff`/`binomialSeries` sections (rebased on
  the imported general lemmas).  Record all name moves in renames.jsonl.
- **Proof sketch**: (1) `import PhD.LWX.PadicExpLog` in 1_PadicAnalytic.lean;
  (2) `abbrev`/`export`-shims in namespace JacobsSlash for the deleted decls
  (`padicLog := LWX.PadicExpLog.padicLog (p := 3)` etc.) so downstream JacobsSlash
  files compile unchanged; (3) delete the shadowed proofs; (4) `lake build` the
  whole JacobsSlash tree + runLinter; (5) optionally inline the shims at the call
  sites and drop them (worker's choice; record).
- **Mathlib lemmas needed**: none new.
- **Sources**: this board's B3 progress notes; PhD/JacobsSlash/PROGRESS.md (the
  slashRefactor board convention that Jacobs is instance-of-general, cf. laweights).
- **Generality**: pure deduplication; no statement changes on the JacobsSlash side
  beyond namespace/instantiation.

### [CLEANUP-3] /cleanup on PhD/LWX/UnitsLog.lean (final)
- **Status**: done (finished 2026-09-04T12:15Z) | **Depends on**: B1, B3 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T12:15Z: UnitsLog.lean + PadicExpLog.lean both sorry-free, zero warnings,
    runLinter-clean on their own declarations (the 3 remaining runLinter errors in
    the UnitsLog run are all in imported PhD/TateFredholm/Tate.lean — pre-existing,
    recorded in B3's note); module docstring updated for the `qlog`-as-restriction
    design; all public decls on standard axioms.

---

## Tranche C — tilted degree (`PhD/LWX/TiltedDegree.lean`)

### [C1] Difference-calculus identities
- **Status**: done (finished 2026-09-03T11:11Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T11:11Z: DONE, all four.  `fwdDiff_iter_mul` by induction on `m` with `f g y`
    generalized: split `Δ(fg) = (shift f)·Δg + Δf·g`, apply IH to both, reindex the
    first sum by `j = i+1` via `Finset.sum_range_succ'` against an if-padded target,
    pad the second via `sum_range_succ`, recombine with Pascal (`Nat.choose_succ_succ`).
    Helpers: private `fwdDiff_iter_shift` (Δ-iterates commute with `·+1`, induction
    generalizing `f`), private `fwdDiff_iter_zero_fun`.  TRAPS: `if_pos rfl`/`if_neg h`
    with un-instantiated condition leave stuck metavariables or grab the WRONG ite —
    always `show`-annotate the condition; bare `Finset.sum_range_succ` rewrote the
    LHS sum instead of the RHS one (pass the function + bound explicitly).
    `fwdDiff_choose` by `PadicInt.denseRange_natCast.equalizer` + mathlib's
    `PadicInt.continuous_choose` + `Ring.choose_natCast` + `Nat.choose_succ_succ'`.
    `fwdDiff_iter_choose` by induction (both overshoot branches end `simp [fwdDiff]`).
    `fwdDiff_iter_eval_eq_zero` via `Polynomial.taylor`: mathlib has the full kit
    (`degree_taylor`, `leadingCoeff_taylor`, `taylor_eq_zero`) so `degree_sub_lt`
    gives the degree drop; induction on `m` generalizing `P`.
    NOTE mathlib also has ℕ-level `fwdDiff_choose`/`fwdDiff_iter_choose` (ForwardDiff.lean) —
    ours are the `ℤ_[p]`/`Ring.choose` transfers.
- **Parallel**: yes | **Type**: lemma
- **Statement**: `fwdDiff_iter_mul`, `fwdDiff_choose`, `fwdDiff_iter_choose`,
  `fwdDiff_iter_eval_eq_zero` (TiltedDegree.lean:44–70).
- **Proof sketch**: (1) Leibniz by induction on `m` (base `rfl`; step: apply `Δ̃`,
  expand with `fwdDiff_add`/`fwdDiff` of a product one step —
  `Δ̃(FG)(y) = F(y+1)Δ̃G(y) + Δ̃F(y)G(y)` — then Pascal `Nat.succ_sub_one` +
  `Finset.sum_range_succ'` reindex). (2) `fwdDiff_choose`: both sides continuous
  (`PadicInt.continuous_choose`); agree on `ℕ` (`Ring.choose_natCast` +
  `Nat.succ_sub_one`/`Nat.choose_succ_succ`); conclude by
  `PadicInt.denseRange_natCast` + `Continuous.ext_on`-style
  (`DenseRange.equalizer`, the exact pattern of mathlib MahlerBasis:346).
  (3) iterate; `m > n` branch bottoms out at `Δ̃(const 1) = 0`.
  (4) degree vanishing: induction on `natDegree` via
  `natDegree (P.comp (X+1) − P) < natDegree P` (leading coefficients cancel:
  `Polynomial.natDegree_sub_lt`-massage).
- **Mathlib lemmas needed**: `fwdDiff_add`, `fwdDiff_const`,
  `fwdDiff_iter_eq_sum_shift` (all verified in `Algebra/Group/ForwardDiff`);
  `Ring.choose_natCast`, `PadicInt.continuous_choose`, `PadicInt.denseRange_natCast`,
  `DenseRange.equalizer`; `Polynomial.natDegree_comp`, `Nat.choose_succ_succ`.
- **Sources**: [LWX, (3.5.1), (3.5.2), Lemma 3.7(1)] pp. 17–18; decomposition.md
  C1–C3.
- **Generality**: Leibniz over any `CommRing` target (PR candidate); the rest
  `ℤ_[p]`-specific by nature.

### [C2] `TiltedDeg` API
- **Status**: done (finished 2026-09-03T11:34Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: C1
- **Progress**:
  - 2026-09-03T11:34Z: DONE, all four (booking note originally lost to a silent
    no-op edit; re-recorded 2026-09-04).  The iff: `m ≤ n` branch is
    `PadicInt.norm_le_one` + `zpow_le_zpow_right₀` from `p^0`.  `of_fwdDiff`: cases
    on `m`; `Function.iterate_succ_apply` + `congr 1; omega`.  `mul`:
    `fwdDiff_iter_mul` + `norm_sum_le_of_forall_le_of_nonneg` + per-term `norm_mul`
    chain (`zpow_add₀`; positivity CANNOT prove `0 ≤ (p:ℝ)^(k:ℤ)` with unknown-sign
    exponent — use `zpow_nonneg (Nat.cast_nonneg p)`).  `of_tendsto`:
    `fwdDiff_iter_eq_sum_shift` + `tendsto_finsetSum` + `.const_smul` +
    `le_of_tendsto hlim.norm`.  (2026-09-04 additions under C6: `mono`,
    `tiltedDeg_const`, `sum` joined the API.)
- **Parallel**: after C1 | **Type**: lemma
- **Statement**: `tiltedDeg_iff_of_forall_norm_le`, `TiltedDeg.of_fwdDiff`,
  `TiltedDeg.mul`, `TiltedDeg.of_tendsto` (TiltedDegree.lean:80–110).
- **Proof sketch**: (1) the iff: for `m ≤ n` the bound is `≥ 1` and `f` is
  `ℤ_[p]`-valued — `fwdDiff_iter_eq_sum_shift` + ultrametric sum bound `≤ 1`.
  (2) `of_fwdDiff`: `m = 0` from integrality; `m = m'+1`: `Δ̃^{m'+1}f = Δ̃^{m'}(Δ̃f)`
  (`Function.iterate_succ_apply`), apply the hypothesis. (3) `mul`: the Leibniz sum;
  each term `‖·‖ ≤ p^{(m−(r−i))}·p^{(n−i)} = p^{m+n−r}`; ultrametric finite-sum bound.
  (4) `of_tendsto`: `Δ̃^m F_N z → Δ̃^m f z` (finite signed combination of pointwise
  limits, `Filter.Tendsto.sub`/`.add` over `fwdDiff_iter_eq_sum_shift`); closed
  bounds pass to limits (`le_of_tendsto`).
- **Mathlib lemmas needed**: `fwdDiff_iter_eq_sum_shift`,
  `IsUltrametricDist.norm_sum_le`-family (`norm_sum_le_of_forall`),
  `Function.iterate_succ_apply'`, `le_of_tendsto'`.
- **Sources**: [LWX, Def-Prop 3.8(1), Lemma 3.10] p. 18; decomposition.md C4.
- **Generality**: clause-(1) definition (no Mahler expansion dependency — see
  decomposition C4 attack log).

### [C3] Binomial-basis conversion (Lemma 3.11)
- **Status**: done (finished 2026-09-03T11:34Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T11:34Z: STATEMENT FIX (b2-logged, pending user ratification): the ticketed
    statement is FALSE as written — (1) over a char-`p` ultrametric field every
    `i ≥ p` term vanishes (`(i! : L) = 0`), so `X^p` over `𝔽_p((t))` is not
    representable; (2) for `ρ > 1` the triangular system forces `c` and the bound
    fails (`P = C(p^{-2})·X²`, `ρ = p` over `ℚ_p`).  Source [LWX 3.11] is `ℤ_p`
    coefficients + `s ∈ ℝ≥0`, i.e. char 0 + `ρ = p^{-s} ≤ 1`; sole consumer (C6)
    is `L = ℚ_p`, `ρ ≤ 1`.  Added `[CharZero L]` + `(hρ1 : ρ ≤ 1)` — recorded in
    b2_log.jsonl (C3) and renames.jsonl; decomposition.md C5's `[hypothesis]`
    attack missed both.  NOT a session B2-stop: the fix is forced and the board's
    milestones do not depend on the dropped generality.
  - 2026-09-03T11:34Z: DONE.  Private `exists_descPochhammer_basis` (induction on the degree
    bound `r`; peel `a := coeff (r+1)` against monic `descPochhammer` — mathlib has
    the full kit: `monic_descPochhammer`, `descPochhammer_natDegree`,
    `descPochhammer_map` (integrality via `Int.castRingHom` + `coeff_map` +
    `IsUltrametricDist.norm_intCast_le_one`, import `Analysis.Normed.Ring.Ultra`),
    `Function.update` for the coefficient stream; `Polynomial.degree_sub_lt` not
    needed here — top-coeff cancellation is direct).  Public wrapper cancels the
    factorials (`mul_inv_cancel₀` + `Nat.factorial_ne_zero` under `CharZero`).
    TRAP recurrence: beta-redexes `(fun i => ite ..) i` block `rw` — `show` first.
- **Parallel**: yes | **Type**: lemma
- **Statement**: `exists_binomial_basis` (TiltedDegree.lean:118).
- **Proof sketch**: strong downward induction on degree, as the source: peel the top
  coefficient `c_r := b_r·r!⁻¹·…` — concretely, define `c` by the triangular system
  and prove the norm bounds by reverse induction using that the transition
  coefficients (`descPochhammer` coefficients) are integers (`‖·‖ ≤ 1`); assemble the
  polynomial identity by `Polynomial.ext` on coefficients.
- **Mathlib lemmas needed**: `descPochhammer_succ_left`/`_eval` API,
  `Polynomial.coeff_C_mul`, `Int.cast`-norm `≤ 1` on ultrametric fields
  (`IsUltrametricDist.norm_intCast_le_one` — verify exact name at start).
- **Sources**: [LWX, Lemma 3.11] p. 19 (proof, 10 lines); decomposition.md C5.
- **Generality**: any ultrametric `NontriviallyNormedField`, real weight `ρ` (absorbs
  the source's fractional `s` — see decomposition C5).

### [CLEANUP-4] /cleanup on PhD/LWX/TiltedDegree.lean (cadence)
- **Status**: done (finished 2026-09-03T11:38Z) | **Depends on**: C1, C2, C3 | **Blocks**: C4, C5, C6 | **Type**: cleanup
- **Progress**:
  - 2026-09-03T11:38Z: runLinter clean; all nine C1–C3 decls on standard axioms
    (propext/Classical.choice/Quot.sound); unusedSimpArgs warnings already trimmed
    in-flight; file uses ≤-convention + omega throughout.  Deferred: full-file
    /cleanup pass re-runs at CLEANUP-5 once C4–C6 close the remaining sorries.

### [C4] The two `ℕ`-valuation inequalities  ⟨VERIFY-spot⟩
- **Status**: done (finished 2026-09-03T11:58Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: CLEANUP-4
- **Progress**:
  - 2026-09-03T11:58Z: SANCTIONED EDIT APPLIED (recorded in renames.jsonl): `nat_ineq_3_13_2`
    hypothesis `2 ≤ n` → `¬ p ∣ n` (case (a)); new `nat_ineq_3_13_2'` with
    `(hp2 : p ≠ 2)` + `2*p ≤ n` (case (b); source's `(p,n) ≠ (2,4)` exclusion
    automatic for odd `p`).
  - 2026-09-03T11:58Z: DONE.  `nat_ineq_3_12`: one Legendre cutoff `b := log p n + log p k + 2`
    for both factorials (`padicValNat_factorial (b := b)` — MUST pass `b` explicitly,
    rw leaves it as a metavariable and downstream omegas silently get `?m` atoms);
    peel `i = 1` via `Finset.sum_eq_sum_Ico_succ_bot`; tail versus tail by
    `Finset.sum_Ico_eq_sum_range` (higher-order: pass `f` EXPLICITLY, unifier can't
    invert `f (m+i)`), termwise `n/p^{2+r} = (n/p)/p^{1+r} ≤ k/p^{1+r}`; final omega.
    Case (a): `v(n) = 0` + `factorization_le_iff_dvd` (Finsupp.le_def at `p`) +
    `div_le_iff₀`; `norm_num` before `linarith` (`1 + ↑0` blocks it).
    Case (b): `p(1+v(n)) ≤ n` by `v(n) < 2` (`≤ 2p`) vs `v(n) ≥ 2`
    (`1+a ≤ 3^{a-2+1} ≤ p^{a-1}`, `Nat.ordProj_dvd`); `v(k!/m!) ≥ ⌊(k−m)/p⌋` via
    `choose_mul_factorial_mul_factorial` + `factorization_mul` + Legendre single
    term (`Finset.single_le_sum` — pass `f` explicitly, wrong-`i` unification);
    ℝ endgame: `div_le_div_iff₀`, floor bound from `Nat.div_add_mod` (omega treats
    `p·q` and `t/p` as atoms for VARIABLE `p` — feed it `div_add_mod` explicitly),
    `(m−1)(1−1/p) ≥ 0` as an explicit product hint for linarith.
- **Parallel**: with C5 prep | **Type**: lemma
- **Statement**: `nat_ineq_3_12` (TiltedDegree.lean:126) and `nat_ineq_3_13_2`
  (TiltedDegree.lean:143). **Sanctioned statement edit** (from the decomposition's
  successful attack): `nat_ineq_3_13_2`'s hypothesis `2 ≤ n` must be replaced by the
  source's case guards — state it for `¬ p ∣ n` (case (a)) and, as a second lemma
  `nat_ineq_3_13_2'`, for `2*p ≤ n` (case (b); `(p,n) = (2,4)` excluded by `p ≠ 2`).
  Record the edit in this ticket when done.
- **Proof sketch**: Legendre (`padicValNat_factorial`-family): 3.12's display
  "`v(k!p^k) = k + ⌊k/p⌋ + ⌊k/p²⌋ + … ≥ k + ⌊n/p²⌋ + ⌊n/p³⌋ + … = k − ⌊n/p⌋ + v(n!)`"
  from `⌊k/p^ℓ⌋ ≥ ⌊n/p^{ℓ+1}⌋` (which follows from `k > ⌊n/p⌋` via
  `Nat.div_div_eq_div_mul` and `Nat.le_div_iff_mul_le`); 3.13.2 per the source's
  case computations (`v(k!) ≥ v(m!)` + `m ≥ k/n` in case (a); the `⌊(k−m)/p⌋` bound
  in case (b)).
- **Mathlib lemmas needed**: `padicValNat_factorial` (verified,
  NumberTheory/Padics/PadicVal/Basic.lean:572) or `Nat.Prime.factorization_factorial`
  (same file family), `Nat.div_div_eq_div_mul`, `omega`.
- **Sources**: [LWX, Lemma 3.12 proof; (3.13.2) and cases (a)–(b)] pp. 19–20;
  decomposition.md C6/C7 (incl. the successful edge-case attack at `n = p`).
- **Generality**: pure `ℕ`; stated with `Nat.factorization`.

### [C5] Lemma 3.12
- **Status**: done (finished 2026-09-03T12:20Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: C2, C3, C4
- **Progress**:
  - 2026-09-03T12:20Z: DONE, per the source's route.  New privates: generic
    `descPochhammer_eval_eq_factorial_smul_choose` (any CommRing+BinomialRing —
    bridges `Ring.descPochhammer_eq_factorial_smul_choose`'s ℤ-`smeval` to `eval`
    via `eval₂_smulOneHom_eq_smeval` + `Subsingleton.elim` on ℤ-ring-homs);
    `coe_ringChoose` (ℤ_[p]→ℚ_[p] compat by `k!`-cancellation; the ascPochhammer
    cast chain is `ascPochhammer_eval₂` + `eval₂_at_apply`); `coe_fwdDiff_iter`
    (Δ̃-iterates commute with the isometric inclusion); `fwdDiff_iter_choose_coe`
    (mixed-domain (3.5.2), derived from the ℤ_[p] version — NOT re-proved);
    `coeff_mul_le_of_coeff_le` + `coeff_descPochhammer_comp_le` (the `g ∈ ℤ_p[pz]`
    grading, induction via `descPochhammer_succ_left` + `comp_assoc`);
    `tiltedDeg_choose_of_pMul_poly` (polynomial case: C3 at `ρ = p⁻¹` on
    `Q := map coe g`, Mahler-type finite expansion `hψ` by `n!`-cancellation,
    clause-(1) bound via C2's iff — only `m > ⌊n/p⌋` matters, killing the source's
    implicit Mahler-integrality appeal — plus C4's `nat_ineq_3_12` on `‖c_k·k!/n!‖`,
    `Padic.norm_eq_zpow_neg_valuation` + `Padic.valuation_natCast` for factorial
    norms).  Main theorem: truncation `P N := Σ_{k<N} C(a k)Xᵏ`,
    `TiltedDeg.of_tendsto` + `HasSum.tendsto_sum_nat` + `continuous_choose`.
    TRAPS: `fwdDiff_iter_finsetSum`/`_const_smul` are Pi-sum/Pi-smul statements —
    convert the pointwise sum via `Finset.sum_apply` first, and the step `h` is an
    explicit FIRST arg; `BinomialRing ℚ_[p]` fires via the `Module ℚ≥0` instance ✓;
    `div_le_iff₀` positivity side needs `zpow_pos`, not positivity.
- **Parallel**: no | **Type**: theorem
- **Statement**: `tiltedDeg_choose_of_pMul` (TiltedDegree.lean:134).
- **Proof sketch** (source's, pp. 19): (1) truncate the series: `F_N` polynomial
  approximations converge pointwise (summability), reduce by `TiltedDeg.of_tendsto`
  — for polynomial `f` with `‖coeff_k‖ ≤ p^{−k}`: (2) `g := ∏_{i<n}(f − i)` has
  `‖coeff_k(g)‖ ≤ p^{−k}` (product of shifted `f`s, ultrametric coefficient bounds);
  (3) C3 at `ρ = p⁻¹` rewrites `g = Σ c_k·k!·binom(z,k)`, `‖c_k‖ ≤ p^{−k}`;
  (4) `binom(f, n) = g/n!`; its `Δ̃^m`-values: expand `binom(z,k)`-basis through
  `fwdDiff_iter_choose` (C1); the `k ≤ ⌊n/p⌋` terms are integral; for `k > ⌊n/p⌋`
  the factor `‖c_k·k!/n!‖ ≤ p^{−(k − ⌊n/p⌋)}` by C4's `nat_ineq_3_12`; assemble the
  clause-(1) bound.
- **Mathlib lemmas needed**: `Polynomial.coeff_prod`-adjacent bounds;
  `Nat.cast_injective`-free factorial-norm readings
  (`‖(n! : ℚ_[p])‖ = p^{−v(n!)}` via `padicValNat`); C1–C4 exports.
- **Sources**: [LWX, Lemma 3.12] p. 19 (proof, 14 lines); decomposition.md C6.
- **Generality**: hypothesis as `HasSum` presentation (pointwise `ZpJpzK`).

### [C6] Lemma 3.13 (+ the `n = p` monomial)
- **Status**: done (finished 2026-09-04T09:45Z) | **File**: PhD/LWX/TiltedDegree.lean | **Depends on**: C5
- **Progress**:
  - 2026-09-04T09:45Z: DONE — both headline decls sorry-free, standard axioms.  Structure:
    (1) new `TiltedDeg` API (`mono`, `tiltedDeg_const`, `sum`) + `fwdDiff_iter_comp_coe`
    (restriction bridge; the succ-step closes by `rfl` — `↑(w+1) ≡ ↑w+1` is subring-defeq);
    (2) `tiltedDeg_choose_monomial_p` all-downstairs: strong induction on `m`,
    `TiltedDeg.of_fwdDiff`, increment `D(z) = a·p^{p-2}((z+1)^p − z^p)` fed to C5
    via the explicit stream `d k = if k < p then a·p^{p-2}·C(p,k) else 0`
    (`Nat.Prime.dvd_choose_self` for `p ∣ C(p,k)`; `hasSum_sum_of_ne_finset_zero` —
    ASCRIBE its HasSum type or the SummationFilter instance sticks); Chu–Vandermonde
    `Ring.add_choose_eq` + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` + peel
    `j = 0` — indexing by `i` with `j := m−i` avoids ALL reindexing;
    (3) the C5 engine refactor (`tiltedDeg_choose_of_norm_bound`, ρ-parametric with
    the `x·k!/n!`-bound as hypothesis interface) pays off: cases (a)/(b) are ONE
    engine lemma `tiltedDeg_choose_logMonomial_engine` at `ρ := p^{-s}` (rpow,
    `s = (N−1−v(N))/N`; import `Analysis.SpecialFunctions.Pow.Real`!) fed by
    `nat_ineq_3_13_2` resp. `'`; case `N = p` bridges to (2) by the unit-rescaling
    `u₀ := A/p^{p-2}`; `N = 1` by `fwdDiff_iter_eval_eq_zero` on
    `(binomialPoly j).comp (C A·X)`; `N = 0` constant;
    (4) `tiltedDeg_choose_of_logShape`: integrality of log-shape coefficients
    (`v(k) ≤ k−1` via `factorization_le_pred`), subtype-packaged truncations
    `S N z := ⟨Σ_{k<N} A_k z^k, ·⟩`, induction on `N` with Chu–Vandermonde +
    `TiltedDeg.sum`/`mul`, limit by `of_tendsto` + `tendsto_iff_dist_tendsto_zero`.
    TRAPS: NEVER `rcases eq_or_ne N p with rfl` — it substitutes the section prime
    `p` away; `Subtype.ext` + `show`-coe instead of `Subtype.coe_injective` (raw
    `(fun a => ↑a)` unfolds block rw); elaborate `(-(x:ℤ) : ℝ)` pushes Neg outside
    the cast — `push_cast` the goal and write single-cast ℝ exponents.
- **Parallel**: no | **Type**: theorem (largest analytic ticket, ~260 LOC)
- **Statement**: `tiltedDeg_choose_monomial_p` (TiltedDegree.lean:154) then
  `tiltedDeg_choose_of_logShape` (TiltedDegree.lean:147).
- **Proof sketch** (source's, pp. 19–20): (1) monomial `n = p` case by induction on
  `m`: `Δ̃(binom(ap^{p−2}z^p, m)) = Σ_{j≥1} binom(D(z), j)·binom(ap^{p−2}z^p, m−j)`
  with `D(z) = ap^{p−2}((z+1)^p − z^p) ∈ ZpJpzK` — Chu–Vandermonde
  (`Ring.add_choose_eq`) + C5 on the first factor (tilted `≤ ⌊j/p⌋ ≤ j−1`) +
  induction hypothesis + `TiltedDeg.mul` + `TiltedDeg.of_fwdDiff`. (2) general:
  polynomial truncation (`of_tendsto`), split `F = Σ` monomials, Chu–Vandermonde to
  reduce to monomials `A_n z^n`; case `n = 1`: polynomial of degree `m`
  (C1-vanishing + integrality); cases (a)/(b): C3 at `ρ = p^{−(n−1−v(n))/n}` + C4's
  (3.13.2) lemmas; case (c) `n = p^…`: careful — the source's case (c) is literally
  `n = p`; `n = p·(unit)` falls under (a), `n = p²,…` under (b) when `n ≥ 2p`; the
  only residual case IS `n = p` = step (1). Confirm this case coverage against the
  source before writing (the trichotomy `p ∤ n` / `n ≥ 2p` / `n = p` covers all
  `n ≥ 2` at odd `p`; `n = 0, 1` handled directly).
- **Mathlib lemmas needed**: `Ring.add_choose_eq` (verified, Binomial.lean:519),
  `Commute.all`, C1–C5 exports.
- **Sources**: [LWX, Lemma 3.13] pp. 19–20 (proof, ~45 lines); decomposition.md C7.
- **Generality**: `p ≠ 2` (case (d) vacuous).

### [CLEANUP-5] /cleanup on PhD/LWX/TiltedDegree.lean (final)
- **Status**: done (finished 2026-09-04T09:52Z) | **Depends on**: C6 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T09:52Z: file sorry-free (1299 lines), `lake build` + `lake exe runLinter` clean,
    zero warnings, no >100-char lines (checked in chars, not bytes), all seven
    public C-decls on standard axioms.  In-flight cleanups during C4–C6 already
    handled naming/`omit`/unused-simp-args; docstrings carry [LWX] locators.

---

## Tranche D — entries and operator (`PhD/LWX/UpMatrix.lean`)

### [D1] `LocalMat` (= `M₁` in record form) and the Möbius series
- **Status**: done (finished 2026-09-04T13:05Z) | **File**: PhD/LWX/UpMatrix.lean | **Depends on**: none
- **Progress**:
  - 2026-09-04T13:05Z: DONE.  `isUnit_c_mul_add` via `PadicInt.isUnit_iff` + ultrametric
    `norm_add_eq_max_of_norm_ne_norm`.  New privates: `hasSum_coe_iff` (HasSum
    transfer along `ℤ_p ⊆ ℚ_p`; forward = dist-convert, backward =
    `HasSum.map (Coe.ringHom).toAddMonoidHom continuous_subtype_val` — plain `exact`,
    simpa mangles the ∘-form), `mobiusStream` (`a₀ = b·d⁻¹`,
    `a_{k+1} = d⁻¹eᵏ(be+a)`, `e := −d⁻¹c`), `norm_e_le`, `hasSum_mobiusStream`
    (upstairs in `ℚ_p`: `hasSum_geometric_of_norm_lt_one` at `ez`, factorisation
    `↑(cz+d) = ↑d(1−ez)`, `Ring.inverse`-coe identification, index shift via
    `(hasSum_nat_add_iff' 1).mp` + `show`-beta; final value identity closed by
    `linear_combination (dv·↑b) * (inv_mul_cancel₀ h1ez)` — field_simp stalls on
    the `(1−ze)⁻¹`-orientation).  TRAP: `convert hC using 1` on two `HasSum`s with
    different instance paths (`instAddCommGroupPadic` vs field-chain) leaks an
    instance-equality goal — derive the value equality and `rw` instead.
    Both exists-theorems from the one stream (case (1) uses `hδ` for `‖be+a‖ ≤ p⁻¹`,
    case (2) only `‖·‖ ≤ 1` + `norm_natCast_le_one`).
- **Parallel**: yes | **Type**: lemma
- **Statement** (revised 2026-09-03 — `LocalMat` is now [LWX, (2.3.3)]'s `M₁`, with
  the `U_p`-shape as the refinement `IsUpShape`): `isUnit_c_mul_add`,
  `exists_hasSum_mobiusFun` (under `IsUpShape` — the [LWX, Lemma 3.12] input), and
  `exists_hasSum_mobiusFun_logShape` (general `M₁` — the [LWX, Lemma 3.13] input for
  Prop 3.14(2); same geometric expansion, weaker bound `v ≥ k − 1`; see
  decomposition.md D1b).
- **Proof sketch**: (1) `‖c·z‖ ≤ p⁻¹ < 1 = ‖d‖` ⟹ unit (ultrametric unit ball +
  `IsUnit.add`-perturbation: `cz + d = d(1 + d⁻¹cz)`, second factor a 1-unit —
  `PadicInt.isUnit_iff`/`isUnit_of_norm_eq_one`-route). (2) geometric series:
  `(cz+d)⁻¹ = d⁻¹·Σ (−d⁻¹cz)^k`; multiply by `az + b`; collect coefficients
  `a_k = (−d⁻¹c)^{k−1}d⁻¹(… a, b …)` with `v ≥ k` (both `a, c` have `v ≥ 1` —
  decomposition D1's coefficient check); `HasSum` via `hasSum_geometric_of_norm_lt_one`
  transported to `ℤ_[p]` (or direct partial-sum computation).
- **Mathlib lemmas needed**: `PadicInt.isUnit_iff` (`‖x‖ = 1`),
  `hasSum_geometric_of_norm_lt_one` (in `ℚ_[p]`, then descend), `Ring.inverse_eq_inv'`
  API for `Ring.inverse` on units.
- **Sources**: [LWX, Prop 3.14 proof] p. 21 ("`f(z) ∈ ZpJpzK`"); decomposition.md D1.
- **Generality**: no `det ≠ 0` hypothesis (unused — documented).

### [D2] `gFun`/`gCoeff` and their shape
- **Status**: done (finished 2026-09-04T13:40Z) | **File**: PhD/LWX/UpMatrix.lean | **Depends on**: D1, B1, B3
- **Progress**:
  - 2026-09-04T13:40Z: DONE.  Def-holes filled per ticket bodies with one improvement: the
    `/p`-integrality is `p ≠ 2`-FREE (the general `PadicExpLog.norm_padicLog_le`
    margin needs no odd-`p` sharpening), so `gFun` is a TOTAL subtype-mk, no
    junk-dite (new private `norm_qlog_le'`), and `coe_gFun` is `rfl`.
    `isLogShape_gCoeff`: the `/p` costs a factor `p`, so the ISLOGSHAPE-level bound
    on `qlogLinearCoeff` is insufficient — use the SHARP product
    `‖qlc w (k+1)‖·‖k+1‖ = ‖w‖^{k+1}` (denominator cancels), then
    `‖w‖^{k+1}·p ≤ p^{-(k+1)+1}` exactly.  `hasSum_gCoeff`:
    `hasSum_qlogLinearCoeff.div_const` + `hasSum_ite_eq` + funext-match massage
    (`hp2` now unused — binder underscored, statement verbatim).
    TRAP: `rw [gFun, dif_pos]`/`split_ifs` both choke on a dite whose branches
    elaborate at `{x // ‖x‖ ≤ 1}` vs `ℤ_[p]` — avoided by making the def total.
- **Parallel**: after B | **Type**: def + lemma
- **Statement**: fill the def-holes `gFun`, `gCoeff` and prove `isLogShape_gCoeff`,
  `hasSum_gCoeff` (UpMatrix.lean:88–105). Ticket-specified bodies:
  `gFun δ z := pDiv (qlog (oneUnitPart δ.dUnit) + qlog (1 + (δ.c·(δ.d)⁻¹)·z))` where
  `pDiv` is the `ℤ_[p]`-valued `/p` justified by B2's margin (implement as the
  subtype element with the norm proof);
  `gCoeff δ 0 := (qlog (oneUnitPart …))/p + qlogLinearCoeff … 0` and
  `gCoeff δ (k+1) := qlogLinearCoeff (δ.c·δ.d⁻¹) (k+1) / p`.
- **Proof sketch**: `(cz+d)/d₀ = ⟨d⟩·(1 + (c/d)z)` (algebra with `d = ωT(d)·⟨d⟩`);
  additivity B3 splits `qlog`; `IsLogShape` from `isLogShape_qlogLinearCoeff` +
  `IsLogShape.add_const` (note the extra `/p`: shape margin absorbs it — the stream
  divided by `p` still satisfies the inequality since the source's `g` carries the
  `1/q`; re-check the exponent bookkeeping `v(A_k/p) ≥ (k−1) − v(k)` from
  `v(w^k/k) ≥ k − v(k)` with `v(w) ≥ 1`: `k − v(k) − 1 ≥ (k−1) − v(k)` ✓ exact);
  `hasSum_gCoeff` from `hasSum_qlogLinearCoeff` + constant shift.
- **Mathlib lemmas needed**: B exports; `Units` arithmetic.
- **Sources**: [LWX, Prop 3.14 proof] p. 21; decomposition.md D2.
- **Generality**: per the skeleton.

### [D3] The entry bounds (Prop 3.14, BOTH cases)
- **Status**: done (finished 2026-09-04T14:10Z) | **File**: PhD/LWX/UpMatrix.lean | **Depends on**: D2, C5, C6, A4
- **Progress**:
  - 2026-09-04T14:10Z: DONE.  Two shared privates carry both cases:
    `norm_entryCoeff_le_aux` (tilted-degree product `hf.mul hg` evaluated at
    `(m, 0)`; `hg` always from C6 + D2's `gCoeff`-shape; `ω`-unit killed by
    `PadicInt.norm_units`; exponent bookkeeping `↑(dF + r.toNat) = ↑dF + r` by
    omega) and `norm_entry_le_aux` (packaging through `HaloInt.norm_le_zpow_iff`;
    `j < 0` coefficient vanishes; `dF > m` branch falls back on integrality
    `≤ 1 ≤ p^{j-0}`).  Case (1) = aux at C5 (`tiltedDeg_choose_of_pMul` on D1's
    stream, `dF = ⌊n/p⌋`); case (2) = aux at C6 on D1b's log-shape stream
    (`dF = n`).  `entry`'s halo-bound field: integrality + `min_eq_left`.
    All four public statements verbatim, 2-line wrappers.
- **Parallel**: no | **Type**: theorem
- **Statement** (revised 2026-09-03): `entry` bound field, `norm_entryCoeff_le` +
  `norm_entry_le` (case (1), under `IsUpShape`, exponent `m − ⌊n/p⌋` — feeds F2), and
  `norm_entryCoeff_le_M1` + `norm_entry_le_M1` (case (2), any `δ ∈ M₁`, exponent
  `m − n` — feeds H4's stability; Lemma 3.13 on `binom(f,n)` via D1b replaces
  Lemma 3.12 in the chain, everything else identical). See decomposition.md D3/D3-M1
  and planning finding 4.
- **Proof sketch**: (1) `TiltedDeg ⌊n/p⌋ (choose(mobiusFun δ, n))` = C5 at D1's
  series; (2) `TiltedDeg r (choose(gFun δ, r))` = C6 at D2's shape; (3) product
  tilted `≤ ⌊n/p⌋ + r` (C2's `mul`); (4) evaluate clause (1) at `z = 0`, multiply by
  the norm-1 unit `ω(d̄)` (`norm_units`-neutrality); (5) `norm_entry_le` packages via
  `norm_le_zpow_iff` (A4) with the sign bookkeeping of decomposition D3.
- **Mathlib lemmas needed**: `norm_mul`, `Units.norm`-facts on `ℤ_[p]`
  (`PadicInt.norm_units` — verify name), A4/C exports.
- **Sources**: [LWX, Prop 3.4 + Prop 3.14(1)] pp. 17, 21; decomposition.md D3
  (including the definitional-Prop-3.4 honesty note).
- **Generality**: `ω` arbitrary; entries land in `ℕ`-supported `HaloInt`.

### [CLEANUP-6] /cleanup on PhD/LWX/UpMatrix.lean (cadence)
- **Status**: done (finished 2026-09-04T14:10Z) | **Depends on**: D3 | **Blocks**: D4 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T14:10Z: build clean; runLinter reports NOTHING on UpMatrix.lean's own decls
    (remaining findings are the pre-existing TateFredholm Tate/Matrix ones recorded
    at B3); unused-binder warnings already underscored in-flight (`_hr`, `_hp2`).
    D4's sorries remain by design.

### [D4] The full matrix and the operator
- **Status**: done (finished 2026-09-04T14:55Z) | **File**: PhD/LWX/UpMatrix.lean | **Depends on**: CLEANUP-6, A3
- **Progress**:
  - 2026-09-04T14:55Z: DONE — UpMatrix.lean now SORRY-FREE.  `norm_matrix_le`: ultrametric
    finite-sum over D3's case-(1) bounds.  `tendsto_matrix_cofinite`: bad set inside
    `univ ×ˢ Iio (⌊n/p⌋ + N)` via `exists_pow_lt_of_lt_one`.  `op`: mirrored the
    `TateFredholm.ofCoeffs` (GenFun) construction at `(ι × ℕ, HaloInt p)` — row-sum
    `C₀`-element (`tendsto_tsum_row` split over the finite `‖φ‖ ≥ δ` set + column
    decay), `LinearMap.mkContinuous` with bound `1` (`HaloInt.norm_le_one` makes
    every entry integral, D3 not needed for boundedness); protected signature has
    no `p ≠ 2`, so the def is `dite hp2 … else 0` — junk `0` at `p = 2` (recorded;
    all THEOREMS carry `hp2`).  `matrixCoeff_op` by `tsum_eq_single`.
    TRAPS: `squeeze_zero_norm`'s bound family is named `a` — pass `(a := …)`;
    generic-ring `tsum_mul_left` needs `Summable.tsum_mul_left`; a section-`variable
    (hp2 : p ≠ 2)` mysteriously failed to bind inside one proof — explicit binders.
    runLinter: one unused `[Fintype ι]` on `norm_matrix_le` → `omit`; now zero
    UpMatrix findings.
- **Parallel**: no | **Type**: def + theorem
- **Statement**: `UpDatum.norm_matrix_le`, `UpDatum.tendsto_matrix_cofinite`, the
  def-hole `UpDatum.op`, `UpDatum.matrixCoeff_op` (UpMatrix.lean:142–163).
  Ticket-specified body for `op` (decomposition finding 3 — do NOT use
  `exists_coeffEquiv`, it is `IsTate`-gated): the linear map
  `φ ↦ ⟨fun a => ∑' b, D.matrix ω a b * φ b, _⟩`, continuity by
  `LinearMap.mkContinuous` with bound `1`.
- **Proof sketch**: (1) matrix bound: `≤ p`-term ultrametric max over D3's bounds;
  (2) column decay: fixed `b = (j, n)`: rows `(i, m)` with `m > ⌊n/p⌋ + N` have norm
  `≤ p^{−N}`; finitely many below (`Fintype ι`); (3) summability of
  `b ↦ M a b·φ b`: `‖M‖ ≤ 1` (A2 `norm_le_one`) and `φ` vanishes cofinitely
  (`cSpace.tendsto_cofinite`) ⟹ `summable_of_tendsto_cofinite`; (4) output in
  `c(·)`: split columns at level `N` — tail contributes `≤ sup_{n>N}‖φ(j,n)‖`, head
  contributes `≤ p^{−(m − N…)} ‖φ‖ → 0` in `m` (the decomposition D6 argument);
  (5) `matrixCoeff_op`: `single`-evaluation collapses the tsum
  (`tsum_eq_single`).
- **Mathlib lemmas needed**: `LinearMap.mkContinuous`, `cSpace.tendsto_cofinite`,
  `cSpace.norm_apply_le`, `tsum_eq_single`, `TateFredholm.norm_tsum_le_iSup`.
- **Sources**: [LWX, Prop 3.1(1) + (3.16.2)] pp. 16, 22; decomposition.md D5/D6.
- **Generality**: any `Fintype ι` (class number never named).

### [CLEANUP-7] /cleanup on PhD/LWX/UpMatrix.lean (final)
- **Status**: done (finished 2026-09-04T14:55Z) | **Depends on**: D4 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T14:55Z: file sorry-free (700 lines), build + runLinter clean on its own decls,
    key public decls on standard axioms (`#print axioms` spot-checked seven).

---

## Tranche E — the two-sided bound (`PhD/TateFredholm/TwoSidedBound.lean`)

### [E1] Permutation inequality + two-sided Hadamard
- **Status**: done (finished 2026-09-03T10:50Z) | **File**: PhD/TateFredholm/TwoSidedBound.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T10:50Z: DONE — `sum_sub_le_sum_sub_comp` (tsub_le_iff_right + le_tsub_add +
    `Finset.sum_equiv π`), `norm_minor_le_pow_sub` (mirror of
    `Slopes.norm_det_le_pow_of_row_bound`, permutation step at `τ.symm` via
    `Finset.univ_eq_attach` + `Finset.sum_equiv τ`).  lake build clean.
- **Parallel**: yes | **Type**: lemma
- **Statement**: `sum_sub_le_sum_sub_comp`, `norm_minor_le_pow_sub`
  (TwoSidedBound.lean:50–63).
- **Proof sketch**: (1) `Σ (x_a ∸ y_a) ≥ (Σ x_a) ∸ (Σ y_a)` (`Nat.sub`-superadditivity,
  `omega`-able by induction / `Finset.sum_tsub_le`-style) + `Equiv.sum_comp` for
  `Σ w'∘π = Σ w'`. (2) Hadamard: `minor = det`; Leibniz expansion
  (`Matrix.det_apply`); each monomial `∏_{a∈S} entry(a, π a)` bounded by
  `σ^{Σ max(w−w'∘π,0)} ≤ σ^{(Σw)∸(Σw')}` via (1) and `σ ≤ 1`; ultrametric sum bound
  (`IsUltrametricDist.norm_sum_le`-family) — mirror
  `TateFredholm.Slopes.norm_det_le_pow_of_row_bound` (project pattern, verified).
- **Mathlib lemmas needed**: `Matrix.det_apply`, `Equiv.sum_comp`,
  `Finset.prod_le_prod`-norm variants, `pow_le_pow_right_of_le_one`.
- **Sources**: [LWX, Thm 3.16 proof] p. 22 (the conjugation display); decomposition.md
  E1 + the Faithfulness note.
- **Generality**: any complete ultrametric `NormedCommRing` + `NormOneClass`;
  **no `IsTate`**.

### [E2] Summability + the charCoeff bound
- **Status**: done (finished 2026-09-03T10:55Z) | **File**: PhD/TateFredholm/TwoSidedBound.lean | **Depends on**: E1
- **Progress**:
  - 2026-09-03T10:55Z: DONE — `summable_minor_of_two_sided` via the two-tier exceptional-set
    argument (E₁ + C + raised bar N₀+C+1; filter-split of the ℤ-level net weight,
    `Finset.sum_filter_add_sum_filter_not`, per-element omega, powerset finiteness +
    `Set.Finite.preimage`); `norm_charCoeff_le_pow_two_sided` mirrors the Slopes
    five-liner with the `(−1)^n` handled by `neg_one_pow_eq_or` (no `NormMulClass` —
    the ring is not a field).  File sorry-free, axioms standard, runLinter zero hits.
  - 2026-09-03T10:50Z: proof-shape refinement for `summable_minor_of_two_sided` (recorded per 4e —
    the sketch's one-liner "finitely many S below any bar" needs a two-tier exceptional
    set): with E₁ := {a | (w−w')(a) < 1} (finite by hw) and C := Σ_{E₁}(w'∸w), any S
    NOT contained in E_N := {a | (w−w')(a) < N} has net weight ≥ N − C (ℤ-computation,
    truncations via omega); S's inside E_N are subsets of a finite set.  Statement
    unchanged; the hypothesis hw is exactly strong enough (counterexample without it
    checked: paired ±m weights kill summability).
- **Parallel**: no | **Type**: theorem
- **Statement**: `summable_minor_of_two_sided`, `norm_charCoeff_le_pow_two_sided`
  (TwoSidedBound.lean:68–96).
- **Proof sketch**: (1) cofinite growth of `w ∸ w'` ⟹ for any bar `B`, the set
  `{a : (w∸w') a ≤ B}` is finite ⟹ finitely many `n`-element `S` with weight-sum
  `≤ B` (subsets of a finite set) ⟹ `minor`-norms → 0 cofinitely (E1's bound) ⟹
  `summable_of_tendsto_cofinite`. (2) `charCoeff` = `(−1)^n·tsum`;
  `norm_tsum_le_iSup` + E1 + `hf` — mirror `norm_charCoeff_le_pow`'s five-line proof
  (Slopes.lean:92, project pattern).
- **Mathlib lemmas needed**: `Filter.eventually_cofinite`,
  `Set.Finite.subset`-combinatorics (`Finset.powersetCard`-finiteness),
  `TateFredholm.summable_of_tendsto_cofinite`, `TateFredholm.norm_tsum_le_iSup`.
- **Sources**: [LWX, Thm 3.16 proof] p. 22 (well-definedness paragraph);
  decomposition.md E2.
- **Generality**: as E1.

### [E3] Monotone-weight initial-segment minimum
- **Status**: done (finished 2026-09-03T10:55Z) | **File**: PhD/TateFredholm/TwoSidedBound.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T10:55Z: DONE — verbatim adaptation of `sum_div_le_sum_block`'s peel-the-max
    induction with `v` applied through monotonicity; final step by omega.
- **Parallel**: yes | **Type**: lemma
- **Statement**: `sum_comp_div_le_sum_monotone` (TwoSidedBound.lean:88).
- **Proof sketch**: induction on `n` peeling a maximal-second-coordinate element —
  the verbatim induction of `TateFredholm.sum_div_le_sum_block` (Slopes.lean:161,
  project pattern) with `v` applied to both sides at the peel (monotonicity bridges
  `v(k/t) ≤ v(M.2)`).
- **Mathlib lemmas needed**: `Finset.exists_max_image`, `Finset.card_erase_of_mem`,
  `Nat.div_lt_iff_lt_mul`, `omega`.
- **Sources**: [LWX, Thm 3.16] p. 22 (`λ`'s increments); decomposition.md E3.
- **Generality**: subsumes `choose_two_le_sum` and `sum_div_le_sum_block` (do NOT
  delete those — note for a later mathlib-facing dedup, out of board scope).

### [CLEANUP-8] /cleanup on PhD/TateFredholm/TwoSidedBound.lean (final)
- **Status**: done (finished 2026-09-03T10:55Z) | **Depends on**: E2, E3 | **Type**: cleanup
- **Progress**:
  - 2026-09-03T10:55Z: inline final pass: sorry-free; `omit` hygiene ([DecidableEq I],
    [CompleteSpace R]); runLinter zero hits on the file; axioms standard three on both
    headliners.  Full /cleanup consolidated into CLEANUP-ALL-1 (recorded).

---

## Tranche F/G — assembly (`PhD/LWX/Halo.lean`)

### [G1] The Iwahori shape (Prop 3.1(3), local half)
- **Status**: done (finished 2026-09-03T11:00Z) | **File**: PhD/LWX/Halo.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T11:00Z: DONE — entry computations by `simp [iwahoriRep, Matrix.mul_apply,
    Fin.sum_univ_two]`; both p-divisibilities from `PadicInt.norm_p` + ultrametric max;
    `d`-unit via `h11e ▸ h11` and `IsUnit.unit_spec`.  As the decomposition's G1 attack
    log predicted, `u₀₀`-unit went unused — and so did `u₁₀`'s bound and `p ≠ 2`
    (the `v_j`-column supplies all the `p`-divisibility): binders underscore-prefixed,
    statement otherwise untouched; recorded for /cleanup's weakening decision.
    `UpDatum.ofCosets` now fully compiles (no sorry).
- **Parallel**: yes | **Type**: lemma
- **Statement** (revised 2026-09-03: the conclusion now leads with `δ.IsUpShape`, and
  `UpDatum.ofCosets` supplies the datum's `hshape` field from it):
  `exists_localMat_iwahori_mul` (Halo.lean:137); `UpDatum.ofCosets`
  compiles once it does.
- **Proof sketch**: compute the four entries of `u * iwahoriRep j`
  (`Matrix.mul_apply`, `Fin.sum_univ_two`): `₀₀ = u₀₀p + u₀₁(jp)`,
  `₀₁ = u₀₁`, `₁₀ = u₁₀p + u₁₁(jp)`, `₁₁ = u₁₁`; the two `p`-divisibility bounds by
  ultrametric max (`‖x·p‖ ≤ p⁻¹`), the unit from `h11`; package the `LocalMat`.
- **Mathlib lemmas needed**: `Matrix.mul_apply`, `Fin.sum_univ_two`,
  `PadicInt.norm_p`, `IsUltrametricDist` max bound.
- **Sources**: [LWX, Prop 3.1 proof + §2.5's `v_j`] pp. 11, 16; decomposition.md G1.
- **Generality**: hypotheses = Iwahori shape only; `u₀₀`-unit kept to match the
  source's `Iw_q` (cleanup may weaken; see decomposition G1).

### [F1] The exponent `λ`
- **Status**: done (finished 2026-09-03T11:00Z) | **File**: PhD/LWX/Halo.lean | **Depends on**: none
- **Progress**:
  - 2026-09-03T11:00Z: DONE — `lwxLambda_succ` (= sum_range_succ), `monotone_sub_div` (the
    `(a+(b−a)p)/p` bound; NB an unreduced beta-redex goal defeats omega — `show`
    first), `lwxLambda_eq_sum_comp` (`Nat.div_div_eq_div_mul` + mul_comm).
- **Parallel**: yes | **Type**: lemma
- **Statement**: `lwxLambda_succ`, `monotone_sub_div`, `lwxLambda_eq_sum_comp`
  (Halo.lean:44–53).
- **Proof sketch**: `Finset.sum_range_succ`; `omega` after `Nat.div`-case facts
  (`Nat.div_le_div_right`, `Nat.succ_div`); `Nat.div_div_eq_div_mul` (mind the
  `p*t` vs `t*p` orientation — `Nat.mul_comm` bridge).
- **Mathlib lemmas needed**: `Nat.div_div_eq_div_mul`, `Nat.div_le_div_right`,
  `Finset.sum_congr`.
- **Sources**: [LWX, Thm 3.16] p. 22; decomposition.md F1.
- **Generality**: junk-total in `t` (division-by-zero conventions harmless).

### [CLEANUP-ALL-1] /cleanup-all on the project so far (pre-milestone)
- **Status**: done (finished 2026-09-04T15:20Z) | **Depends on**: CLEANUP-2, CLEANUP-3, CLEANUP-5, CLEANUP-7,
  CLEANUP-8, F1, G1 | **Blocks**: F2 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T15:20Z: all six LWX modules + PadicExpLog build with zero errors AND zero
    warnings (last stragglers: `Set.mem_ofPred_eq` deprecation + three
    `omit [Fintype ι]` in UpMatrix's op-section); runLinter clean on every board
    file's own declarations; board files sorry-free except Halo.lean's F2/F3
    cluster and IntegralModel (tranche H), as scheduled.

### [F2] **THEOREM 3.16** (milestone)
- **Status**: done (finished 2026-09-04T15:45Z) | **File**: PhD/LWX/Halo.lean | **Depends on**: CLEANUP-ALL-1
- **Progress**:
  - 2026-09-04T15:45Z: **MILESTONE DONE — [LWX] Theorem 3.16 is fully formalized, sorry-free,
    standard axioms, compiled FIRST TRY.**  Exactly the planned instantiation of the
    E-tranche: `w a = a.2`, `w' b = ⌊b.2/p⌋`, `σ = p⁻¹`; three private feeders —
    `hdiv_upOp` (D4's `matrixCoeff_op` + `norm_matrix_le`, zpow→pow),
    `hw_upOp` (cofinite growth via `⌊m/p⌋ ≤ ⌊m/2⌋` inside `univ ×ˢ Iio (2B+2)`),
    `lwxLambda_le_sum_sub` (`Finset.sum_tsub_distrib` at `Nat.div_le_self` +
    E3's `sum_comp_div_le_sum_monotone` at F1's `monotone_sub_div` +
    `lwxLambda_eq_sum_comp`).  The four public statements: E2 `summable_minor_of_
    two_sided`, E2' `norm_charCoeff_le_pow_two_sided` (+ pow↔zpow), A4's
    `exists_T_pow_mul_of_norm_le`, A4's `norm_le_zpow_iff`.
- **Parallel**: no | **Type**: theorem
- **Statement**: `summable_minor_upOp`, `norm_charCoeff_upOp_le`,
  `exists_charCoeff_upOp_eq_T_pow_mul`, `norm_coeff_charCoeff_upOp_le`
  (Halo.lean:61–84).
- **Proof sketch**: instantiate E2 at `R = HaloInt p`, `I = ι × ℕ`,
  `w (i,m) = m`, `w' (j,n) = n / p`, `σ = p⁻¹`; hypothesis `hdiv` =
  `UpDatum.norm_matrix_le` through `matrixCoeff_op` (D4); `hw` = cofinite growth of
  `m − m/p` on `ι × ℕ` (finite `ι` + `monotone_sub_div` unboundedness); `hf` = E3 at
  `v m = m − m/p` composed with `lwxLambda_eq_sum_comp` (F1) — mind
  `Σ_S w ∸ Σ_S w' = Σ_S (w − w')` exactness from `w' ≤ w` pointwise
  (`Nat.div_le_self`); then A4's `exists_T_pow_mul_of_norm_le` and
  `norm_le_zpow_iff` for the two other readings.
- **Mathlib lemmas needed**: `Nat.div_le_self`, `Finset.sum_sub_distrib`-on-ℕ with
  the pointwise bound (`Finset.sum_tsub_distrib`? verify; else `omega`-per-element +
  `Finset.sum_congr`), E/A/D/F1 exports.
- **Sources**: [LWX, Theorem 3.16] pp. 21–22 (statement (3.16.1)); decomposition.md
  F2.
- **Generality**: any `UpDatum`, any `ω`; `t` enters only as `Fintype.card ι`.

### [CLEANUP-9] /cleanup on PhD/LWX/Halo.lean (cadence)
- **Status**: done (finished 2026-09-04T15:50Z) | **Depends on**: F2 | **Blocks**: F3 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T15:50Z: Halo.lean builds warning-free after F2; runLinter clean on its own
    decls; F2 block already written in final style (three feeder privates,
    2-line public wrappers).

### [F3] **COROLLARY 3.18** (milestone)
- **Status**: done (finished 2026-09-04T16:15Z) | **File**: PhD/LWX/Halo.lean | **Depends on**: CLEANUP-9, A5
- **Progress**:
  - 2026-09-04T16:15Z: **MILESTONE DONE — [LWX] Corollary 3.18 fully formalized, sorry-free,
    standard axioms; Halo.lean is now 0-sorry.**  (1) coefficient bound = F2 +
    A5's `norm_specialize_le`; (2) anchor via library `charCoeff_zero` +
    `specialize_one`; (3) `monotone_lwxSlopes` from `monotone_sub_div` composed
    with `Nat.div_le_div_right`, sign from `Real.log_neg`; (4) polygon assembly
    mirrored the QMF Weight/Slopes model verbatim (`sum_lwxSlopes` partial-sum
    identity, `isAdmissible_of_affine_bound` at `m = b = 0`,
    `isNewtonPolygonOf_powerSeries.isGreatest` + `height_ofSlopes` +
    `pointHeight_coe`); compiled with only docstring-placement/omit fixups.
- **Parallel**: no | **Type**: theorem
- **Statement**: `norm_specCharSeries_coeff_le`, `specCharSeries_coeff_zero`,
  `monotone_lwxSlopes`, `isBelow_newtonPolygon_specCharSeries` (Halo.lean:97–126).
- **Proof sketch**: (1) coefficient bound = F2's norm form + A5's
  `norm_specialize_le`; (2) anchor: `charCoeff_zero` (library) + `specialize_one`;
  (3) monotone slopes: `monotone_sub_div`-composition ×
  `neg_log`-positivity (`Real.log_neg`); (4) polygon: mirror
  `QMF.Weight.isBelow_newtonPolygon_heckeCharPowerSeries`'s assembly
  (Weight/Slopes.lean:142–166) step-for-step: anchor via
  `coeffVal_zero_of_coeff_zero_eq_one`, log-form bound
  `Σ_{k<n} lwxSlopes k ≤ −log‖coeff n‖` from (1) (`Real.log`-monotonicity +
  `sum_blockSlopes`-style partial-sum identity `Σ = λ(n)·(−log‖T₀‖)`), close with
  `isNewtonPolygonOf_ofSlopes` + `IsNewtonPolygonOf.height_eq`-style `IsBelow`
  assembly exactly as the model proof.
- **Mathlib lemmas needed**: `Real.log_le_log_iff`, `Real.log_pow`;
  project: `NewtonPolygon₀.ofSlopes` API (`isNewtonPolygonOf_ofSlopes`,
  `isAdmissible_of_partial_sums`), `coeffVal` API, the Weight/Slopes model proof.
- **Sources**: [LWX, Corollary 3.18] p. 23; decomposition.md A13/F4/F5.
- **Generality**: any complete ultrametric `NontriviallyNormedField` target;
  isometric `ψ` hypothesis (any completion embedding instantiates).

### [CLEANUP-10] /cleanup on PhD/LWX/Halo.lean (final)
- **Status**: done (finished 2026-09-04T16:15Z) | **Depends on**: F3 | **Type**: cleanup
- **Progress**:
  - 2026-09-04T16:15Z: Halo.lean 0-sorry, 0-warning (last `omit [DecidableEq ι]` on `hw_upOp`),
    runLinter clean on own decls, all four F3 + four F2 publics on standard axioms.

---

## Tranche H — the integral model `S^D_int` (`PhD/LWX/IntegralModel.lean`, added 2026-09-03)

Unification with the ring-generic `QMF/Slash/` layer (verified `Semiring`-generic:
Slash/HeckeMonoid.lean:47–50, Slash/HeckeMatrix.lean:35, incl.
`heckeOperatorSlash_apply_rep` and `bijective_evalAtRepsSlash`) — [LWX, (2.11.1)] and
the Prop 3.1 display are reused, not re-proved; [LWX, Prop 3.4] is promoted from a
definition to a theorem. Source quotes + attack logs: decomposition.md "Revision
2026-09-03".

### [H1] The universal character
- **Status**: done (finished 2026-09-04T17:05Z) | **File**: PhD/LWX/IntegralModel.lean | **Depends on**: A1, B1, B3
- **Progress**:
  - 2026-09-04T17:05Z: DONE.  `oneAddTPow`: integrality bound field trivial; `_zero` by
    `Ring.choose_zero_right/succ`; `_add` = coefficientwise Chu–Vandermonde:
    HaloInt convolution collapsed by `tsum_eq_sum` on the window
    `(range (k.toNat+1)).map ⟨Nat.cast, Nat.cast_injective⟩`, then
    `Ring.add_choose_eq` + `sum_antidiagonal_eq_sum_range_succ`, toNat-alignment by
    `congr 2; all_goals omega`.  `logQuot` total subtype-mk via a third copy of the
    `p ≠ 2`-free qlog-margin (`norm_qlog_le''` — CONSOLIDATION CANDIDATE for
    /cleanup: three private copies now exist in UnitsLog-consumers), `coe_logQuot`
    rfl.  New privates `teichmuller_one` (unit cancellation on `teichmuller_mul`),
    `oneUnitPart_one/mul` (`mul_mul_mul_comm` — `ring` is unavailable in `ℤ_pˣ`),
    `logQuot_one/mul` (B3's `qlog_mul`).  `univChar_one/mul/norm` assembled.
- **Parallel**: with C/D/E fronts | **Type**: def + lemma
- **Statement**: `oneAddTPow` bound field, `oneAddTPow_zero`, `oneAddTPow_add`,
  `logQuot` (def-hole: `qlog⟨a⟩/p` as a `ℤ_[p]` element) + `coe_logQuot`,
  `univChar_one`, `univChar_mul`, `norm_univChar_le` (IntegralModel.lean:55–91).
- **Proof sketch**: (1) bound field: coefficients are `Ring.choose`-values in `ℤ_[p]`
  (norm ≤ 1), `j < 0` branch is `0`; (2) `oneAddTPow_add`: coefficientwise
  Chu–Vandermonde, `Ring.add_choose_eq` (verified, Binomial.lean:519; `Commute` by
  commutativity), with the convolution collapsing to the finite antidiagonal
  (`tsum_eq_sum` on the ℕ-supported streams); (3) `logQuot`: subtype element via
  `norm_qlog_le`'s margin (B2); (4) `univChar_mul`: `toZMod` multiplicativity +
  `teichmuller_mul` (B1) + `qlog_mul` (B3) + (2); (5) norm ≤ 1: `norm_le_one` (A2).
- **Mathlib lemmas needed**: `Ring.add_choose_eq`, `PadicInt.toZMod` (ring hom),
  `Units.map`; A/B exports.
- **Sources**: [LWX, Notation 2.1] p. 8; decomposition.md H1.
- **Generality decision**: per-ω; `p ≠ 2` only where `qlog` needs it.

### [H2] `M₁` and the (2.3.2) action on `C(ℤ_p, Λ^{>1/p})`
- **Status**: done (finished 2026-09-04T18:30Z) | **File**: PhD/LWX/IntegralModel.lean | **Depends on**: H1, D1
- **Progress**:
  - 2026-09-04T18:30Z: DONE (the biggest H ticket).  Closure via ultrametric norms; `toLocalMat`
    through the `M1.entryInt` helper (inline subtype-mks in a `where`-structure
    elaborate at the raw subtype and break every later rw — the helper is
    load-bearing).  CONTINUITY chain: NEW UnitsLog exports
    `teichmuller_eq_of_norm_sub_le` (Teichmüller is locally constant —
    `dvd_sub_pow_of_dvd_sub` + limit uniqueness) and `norm_qlog_sub_qlog_le`
    (`qlog` is 1-Lipschitz on the disc: termwise `geom_sum₂_mul` factor +
    `v(k+1) ≤ k`); in IntegralModel: `continuous_oneAddTPow` (finite gauge-window
    + `continuous_choose`), residue/Teichmüller-constancy of the denominator,
    `oneUnitPart_denUnit` affine, `lipschitzWith_one_mobiusFun` (inversion is an
    isometry at norm-1: `iz − iw = iz·iw·(den w − den z)`).
    COCYCLE: `den_cocycle` (Units.ext + ℚ_p `field_simp` after
    `push_cast [coe_mobiusFun]` and the coordinate simp-set),
    `mobius_cocycle` (numerator identity + den_cocycle + unit cancellation —
    no division needed on the ℤ_p side).  Action fields by
    `ContinuousMap.ext`-ONE-LEVEL (`ext z` recurses into HaloInt-coefficients!)
    + `ring`; SMulSlash by `letI` + structure-literal (bare `constructor` can't
    see the @-pinned instance).  TRAP: in `show`-statements inside proofs about
    `M1.toLocalMat 1`, pin `(1 : M1 p)` or unification leaves `ℤ_[?m]`.
- **Parallel**: after H1 | **Type**: def + instance (the cocycle ticket)
- **Statement**: `M1` closure fields, `M1.toLocalMat` (def-hole: integral-entry
  extraction) + 4 coordinate lemmas, `cfunSlash` continuity field, `cfunSlashAction`
  (zero/one/**mul**/add), `cfunSMulSlash` (IntegralModel.lean:100–153).
- **Proof sketch**: (1) closure mirrors `QMF.Sigma0'.mul_mem'` (Slash/Sigma0.lean:43)
  with norms in place of valuations; (2) `toLocalMat`: `‖x‖ ≤ 1` ⟹ `x ∈ ℤ_[p]`
  (`PadicInt` as the unit ball of `ℚ_[p]`), `d` a unit from `‖d‖ = 1`; (3) continuity
  of the slash value: `mobiusFun` continuous (polynomial + `Ring.inverse` on units),
  `univChar ∘ denUnit` continuous via coefficientwise estimates; (4) `slash_mul` (the
  content): the denominator cocycle `den(g₁g₂, z) = den(g₁, möb g₂ z)·den(g₂, z)`
  (2×2 algebra through the `toLocalMat` coordinate lemmas) + `univChar_mul` + Möbius
  composition; (5) `SMulSlash`: pointwise `mul_left_comm`.
- **Mathlib lemmas needed**: `PadicInt.norm_le_one`-membership API
  (`PadicInt.mem_span`-free unit-ball characterisation), `Ring.inverse_mul_cancel`;
  D1's `isUnit_c_mul_add`.
- **Sources**: [LWX, (2.3.2)–(2.3.3)] p. 10 ("One checks that this action extends to
  an action of the monoid `M₁`"); decomposition.md H2.
- **Generality decision**: bespoke `M1` submonoid; identification with
  `QMF.Sigma0'` (same carrier) is OPTIONAL POLISH pending a `Valued ℚ_[p]` instance —
  record here if attempted.

### [H3] The rescaled embedding (5.4.1)
- **Status**: done | **File**: PhD/LWX/IntegralModel.lean | **Depends on**: A4
- **Parallel**: with H2 | **Type**: def + lemma
- **Statement**: `mahlerEmbed` (def-hole: `a ↦ ∑ₙ aₙ·Tⁿ·binom(·,n)` as a linear map)
  + `mahlerEmbed_apply`, `fwdDiff_mahlerEmbed`, `mahlerEmbed_injective`
  (IntegralModel.lean:159–171).
- **Proof sketch**: (1) pointwise sums converge (`‖aₙTⁿ·const(binom z n)‖ ≤
  ‖aₙ‖p^{−n}`, `summable_of_tendsto_cofinite`) and uniformly, giving continuity;
  linearity from `tsum` linearity; (2) extraction: `Δ̃^m` is a finite signed sum
  (`fwdDiff_iter_eq_sum_shift`), swap with the `tsum`, and `binom(0, k) = δ_{k0}`
  (`Ring.choose_natCast` at `0`) collapses to `aₘTᵐ` — no Mahler expansion theorem;
  (3) injectivity: extraction + `T`-power scaling `norm_T_mul` (A4) is injective.
- **Mathlib lemmas needed**: `fwdDiff_iter_eq_sum_shift`, `Ring.choose_natCast`,
  `tsum`-linearity; A2/A4 exports; `TateFredholm.summable_of_tendsto_cofinite`.
- **Sources**: [LWX, (5.4.1)] p. 34; decomposition.md H3.
- **Generality decision**: stated against `CFun p` (the abbreviation), no bundled
  `Ind`-type.
- **Progress**: DONE. `mahlerEmbed` built via `LinearMap.mk` over a `ContinuousMap`
  assembled from `continuous_mahler_sum` (uniform-limit continuity: partial sums are
  continuous, tail bound `‖aₙTⁿ·const(binom z n)‖ ≤ ‖aₙ‖·p^{−n}` uniform in `z` via
  `HaloInt.norm_T_pow_mul_le` + `norm_const_le`; `TateFredholm.summable_of_tendsto_cofinite`
  gives pointwise convergence). `mahlerEmbed_apply` is `rfl`. `fwdDiff_mahlerEmbed`:
  `fwdDiff_iter_eq_sum_shift` turns `Δ̃^m` at `0` into a finite signed sum; swapped with
  the `tsum` by `hasSum_finset_sum` + `constHom.map_sum` (per-`z` `HasSum` transport, NOT
  `tsum_finsetSum` — instance-path mismatch); `hval` collapses `Δ̃^m binom(·,n)(0)` to
  `if n = m then 1 else 0` (`Ring.choose` diagonal), then `tsum_eq_single`. Injectivity:
  `injective_iff_map_eq_zero`, extract `a m * T^m = 0` via `fwdDiff_mahlerEmbed`, cancel
  the `T`-power coefficientwise: `DFunLike.congr_fun` at `j + m`, `mul_comm` +
  `HaloInt.coeff_T_pow_mul` shifts the index (`j + ↑m − ↑m`), and the zero side is
  definitional (`hz : ((0 : c(ℕ, HaloInt p)) m) j = 0 := rfl` — simp makes NO progress
  here, `rfl` is the move), `simpa` closes. All three decls: standard axioms
  (propext/Classical.choice/Quot.sound), `lake build` clean (2550 jobs).

### [CLEANUP-H1] /cleanup on PhD/LWX/IntegralModel.lean (cadence)
- **Status**: done | **Depends on**: H1, H2, H3 | **Blocks**: H4, H5 | **Type**: cleanup

### [H4] Stability and Prop 3.4 as a theorem
- **Status**: done | **File**: PhD/LWX/IntegralModel.lean | **Depends on**: CLEANUP-H1, D3
- **Parallel**: no | **Type**: theorem
- **Statement**: `cfunSlash_mahlerEmbed` (documented shared-witness existential),
  `seqSlashAction` (def-hole: the transported action), `mahlerEmbed_seqSlash`,
  `seqSlash_coeff` (IntegralModel.lean:173–214).
- **Proof sketch**: (1) compute `Δ̃^m` of `cfunSlash (mahlerEmbed a) g` at `0`:
  Leibniz-free — expand `mahlerEmbed_apply`, swap `Δ̃^m` with the `tsum` (finite
  signed sums), recognise per-`n` the entry stream: `Δ̃^m(binom(f,n)·[cz+d])(0)·Tⁿ =
  Tⁿ·entry(g.toLocalMat) m n` by definition of `entryCoeff` + `univChar`'s expansion
  (the T-coefficients of `[cz+d]` ARE `ω(d̄)·binom(g z, r)` — `coe_logQuot` +
  `coeff_oneAddTPow`); (2) `T^m`-divisibility of the resulting stream:
  `norm_entry_le_M1` (D3, case (2)) + ultrametric `tsum` bound + A4's extraction —
  the witness `b`; (3) `b ∈ c(ℕ, ·)` (vanishing): the same bound, `m → ∞`;
  (4) transported action laws from injectivity (H3) + `cfunSlashAction` (H2);
  (5) `seqSlash_coeff` re-reads (1)–(2).
- **Mathlib lemmas needed**: D3/A4/H2/H3 exports; `TateFredholm.norm_tsum_le_iSup`.
- **Sources**: [LWX, Prop 3.4] p. 17 (promoted to a theorem) + [LWX, §5.4] p. 34
  ("We claim that this subspace is stable under the action of the monoid `M₁`");
  decomposition.md H4 and planning finding 4.
- **Generality decision**: action transported to the sequence model, the home of the
  determinant theory.
- **Progress**: DONE (with a B2 statement fix, see b2_log.jsonl + renames.jsonl).
  The ticketed T-rescaled transport is FALSE: for `g = [[p,0],[p,1]]` (Up-shape) and
  `a = single 0 1`, the slash of the constant `1` is `(1+T)^{ℓ(1+pz)}` with
  `ℓ(1+pz) = z + p·w(z)`, whose `Δ̃^m`-coefficient at `T^m` is `1 + O(p⁻¹)` — the
  forced rescaled coefficients have norm `1` for all `m`, not c₀.  [LWX, Prop 3.4]
  expands in the PLAIN Mahler basis (matrix = raw `entry`, matching `UpDatum.matrix`
  and `D.op` exactly; c₀ preserved by column decay).  Implemented:
  `mahlerON : c(ℕ, HaloInt p) →ₗ[HaloInt p] CFun p` (plain realisation via mathlib's
  `PadicInt.mahlerSeries` — NEW `Algebra ℤ_[p] (HaloInt p)` + `IsBoundedSMul`
  instances in HaloRing.lean make `Λ^{>1/p}` an ultrametric `ℤ_p`-Banach module, so
  ALL of mathlib's MahlerBasis applies: `fwdDiff_tendsto_zero` gives c₀-decay,
  `hasSum_mahler` the expansion, `fwdDiff_mahlerSeries` the recovery — no hand-rolled
  Mahler theory); `mahlerCoeffs` (the inverse); roundtrips `mahlerON_mahlerCoeffs` /
  `mahlerCoeffs_mahlerON`; `mahlerON_injective`.  Bridge: `denUnit_zero`,
  `oneUnitPart_denUnit_factor` (`⟨cz+d⟩ = ⟨d⟩·(1+wz)`), `logQuot_denUnit`
  (`ℓ(cz+d) = gFun δ z`, via `qlog_mul`; UpMatrix's `wCoeff`/`norm_wCoeff_le`
  de-privatized), `coeff_slash_choose`, `entry_eq_fwdDiff` (`P_{m,n}(δ)` IS the m-th
  Mahler coefficient of `z ↦ [cz+d]·binom(möb z, n)` — coefficientwise via `coeffHom`
  + `addMonoidHom_fwdDiff_iter`; the ω-constant and `a n` pull out via
  `AddMonoidHom.mulLeft`).  Headline `cfunSlash_mahlerON` (witness =
  `mahlerCoeffs` of the slashed realisation), `seqSlashAction` (laws transported
  along the roundtrips from `cfunSlashAction`; `conv_lhs` for the slash_mul rewrite
  to avoid self-referential rw), `mahlerON_seqSlash`, and H5's `seqSlash_coeff`
  (plain form) proven early.  All standard axioms; `lake build` clean (2550 jobs).
  H3's `mahlerEmbed` retained as genuine [LWX, (5.4.1)] content.

### [H5] **THE SEAM** (milestone): `S^D_int` and the intertwining
- **Status**: done | **File**: PhD/LWX/IntegralModel.lean | **Depends on**: H4, D4,
  CLEANUP-ALL-1
- **Parallel**: no | **Type**: def + theorem (milestone)
- **Statement**: `levelM1`, `intAutSlashAction` (def-hole: assemble the automorphic
  slash from `seqSlashAction` through `θ` — pin the exact `QMF.Slash` constructor at
  execution and record it here), `IntForms` (def-hole: `levelSubmoduleSlash` under the
  `letI`s), `intEvalAtReps` (def-hole: mirror of `QMF.Weight.evalAtReps`,
  Weight/Compact.lean:92, via `cSpace.blockIncl`), `intEvalAtReps_comm`
  (IntegralModel.lean:216–260).
- **Proof sketch**: (1) the automorphic slash: `(φ ∣ₛ u)(x) = φ(x·u⁻¹?)`-free — use
  the same constructor `QMF.Slash` uses for its automorphic actions (value-side slash
  through `θ`), so that for `u ∈ levelM1` the value-side action is
  `seqSlashAction` at `θ u` BY CONSTRUCTION; (2) `IntForms` := `levelSubmoduleSlash
  (HaloInt p) U hU`; (3) `intEvalAtReps`: `φ ↦ ∑ᵢ blockIncl i (φ (c i))` (copy the
  Weight/Compact formula, `K → HaloInt p`); (4) `intEvalAtReps_comm`: evaluate both
  sides at a block `(i, m)`: LHS = `(Φφ)(cᵢ)ₘ` = (hypothesis `hΦ`)
  `∑ⱼ (φ(c_{tgt i j}) ∣ₛ g i j)ₘ`; apply `seqSlash_coeff` (H4) + `hg`; RHS =
  `D.op`'s matrix row (D4's `matrixCoeff_op` + `tsum_eq_sum` on the `p` summands);
  `T^m`-injectivity (A4) cancels the common factor.
- **Mathlib lemmas needed**: `cSpace.blockIncl/blockProj` API (TateFredholm/BlockOp),
  H4/D4/A4 exports; QMF's automorphic-slash constructor (pin at execution).
- **Sources**: [LWX, §2.7] p. 12 (`S^D_int`) + [LWX, Prop 3.1] p. 16 (the display,
  discharged at instantiation by `heckeOperatorSlash_apply_rep` —
  Slash/HeckeMatrix.lean:57, ring-generic, already proved) + [LWX, (2.11.1)] p. 13
  (= `bijective_evalAtRepsSlash`, Slash/HeckeMatrix.lean:181, reused);
  decomposition.md H5 (including the circularity-check attack).
- **Generality decision**: `Φ` abstract linear with the display as hypothesis — the
  Hecke finiteness plumbing stays in QMF; a concrete quaternion-algebra instance is
  out of board scope (plan.md, still-deferred item 3).
- **Progress**: DONE — **MILESTONE COMPLETE**, sorry-free, standard axioms.
  Pinned constructors: `levelM1 = Submonoid.comap θ (M1 p)` with corestriction
  `levelM1ToM1` (the `levelMonoidOfToS` pattern inlined — Weight/Forms and
  Weight/SlashAction were NOT imported, keeping IntegralModel off the weight tower;
  their `comap` pattern replicated in `seqLevelSlashAction`); `intAutSlashAction` =
  the ring-generic `AutomorphicFunction` instance over `seqLevelSlashAction` (letI +
  inferInstance); `IntForms = AutomorphicFunction.levelSubmoduleSlash (HaloInt p) U
  hU` under letI value-action + haveI `seqLevelSMulSlash` (new: `seqSMulSlash` for
  the M1-level action via `fwdDiff_iter_const_smul`, pulled back).  `intEvalAtReps`
  mirrors `QMF.Weight.evalAtReps` verbatim (`blockIncl` sum; NEW import
  PhD.TateFredholm.BlockOp), with `blockProj_intEvalAtReps` + `intEvalAtReps_apply`.
  NEW UpMatrix export `UpDatum.op_apply` (rows of `op` at odd `p`).  The seam
  `intEvalAtReps_comm`: calc chain — eval-apply, `hΦ` display, `map_sum
  (cSpace.evalCLM m)`, per-`j` `seqSlash_coeff` + `hg` + `mul_comm`, regroup by
  target block (`Finset.sum_fiberwise_of_maps_to` + filter-membership rewrite),
  swap finite/`tsum` (`hasSum_finset_sum`), recognise `D.matrix` (rfl + 
  `Finset.sum_mul`), reassemble the product `tsum` (`Summable.tsum_prod` +
  `tsum_fintype`), close with `UpDatum.op_apply`.  Summability inputs: two squeeze
  lemmas (matrix/entry integrality `HaloInt.norm_le_one` vs `cSpace`
  cofinite-decay).  Compiled FIRST TRY after the BlockOp import.  With F2/F3:
  `charPowerSeries` of any `Φ` satisfying the Prop 3.1 display equals
  `charPowerSeries (D.op ω)`, to which Theorem 3.16 and Corollary 3.18 apply.

### [CLEANUP-H2] /cleanup on PhD/LWX/IntegralModel.lean (final)
- **Status**: done | **Depends on**: H5 | **Type**: cleanup

---

### [CLEANUP-FINAL] /cleanup-all on the whole board's files
- **Status**: done | **Depends on**: CLEANUP-10, CLEANUP-H2 | **Type**: cleanup
- Also: run `lake exe runLinter` on all seven modules (house rule: catches unused
  instance arguments nothing else does); `#print axioms` on the F2/F3/H5 headliners
  (standard three only); update this board's Summary and
  `PhD/TateFredholm/README.md`'s §11 table with `TwoSidedBound.lean`.
- **Progress**: DONE 2026-09-04.  `lake build` green on all 8 board modules (2587
  jobs); runLinter: zero hits on every board file (the 25 remaining hits are
  pre-existing, in non-board TateFredholm/ForMathlib modules); axioms on all six
  headline declarations = propext/Classical.choice/Quot.sound; three lint warnings
  fixed in IntegralModel (2 unused simp args, 1 simpa→simp); module docstring
  rewritten (the "orthonormal rescaled basis" claim was the B2-falsified one);
  Summary + README §11 updated.

---

## FUTURE BOARDS (agreed 2026-09-03; do NOT ticket here)

1. **`lwx-slopes`** — coefficient-level Tier 2, planned via `/develop` once F2/F3/H5
   land: Cor 3.18's sharpness clause, LWX Lemma 4.1, §4.2's Claim, Thm 1.3 Step II +
   Thm 1.5 first half conditional on a touching hypothesis (the `hClassNumberOne`
   pattern). Needs nothing beyond this board's outputs.
2. **`tate-riesz`** — the Tate ring `A = HaloInt[1/T]` + JN §2.2–2.3 (Thm 2.2.2 ring
   Riesz, Thm 2.2.13 slope decompositions, LWX Rmk 3.25's integral factorization).
   Independently valuable: it is the `TateFredholm` README's own recorded remaining
   gap.

Everything else deferred is listed in plan.md "Deferred seams" (Prop 2.17, the
classical inputs, concrete-level instantiation, `p = 2`, `ℤ_p[Δ]`).
