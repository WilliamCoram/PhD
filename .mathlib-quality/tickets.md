# Ticket Board — Weierstrass division & preparation (Option B, Tranche 1)

## Summary
- Total: 36 tickets (23 proof/def + 12 cleanup + 1 experimental probe)
- Open: 36 | In Progress: 0 | Done: 0
- Parallel capacity: 2 workers early (Distinguished ∥ Rescale-helpers), then mostly serial
  (single dependency spine).
- Skeleton: all statements already exist as `:= by sorry` declarations; every proof ticket is
  "fill the sorry at the named declaration". Statements are canonical — do not restate.
- Conventions: [[restricted-seam-convention]] (term-mode across the `Restricted` seam);
  weights at `c = 1` bridge by `one_pow`/`simp`; general-`c` lemmas applied at `1` may need
  explicit `(c := 1)`.
- Sources are machine-checked Lean files; "Source" fields give `file:lines`. On any
  proof-sketch failure, hard-stop per `/beastmode` rules and record to b2_log.

## Tickets

### [T001] Distinguished basics: `ne_zero`, `norm_coeff_mul_pow_eq`, `norm_pos`
- **Status**: done (2026-07-25; 3/3 proven, standard axioms; norm_pos via congrArg-val not val_zero-rw; per-decl cleanup deferred to CLEANUP-1 per board design) | **File**: `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/Distinguished.lean`
- **Depends on**: none | **Parallel**: yes (with T004+) | **Type**: lemma ×3
#### Statement
Skeleton `Distinguished.lean` — `IsDistinguished.ne_zero`, `IsDistinguished.norm_coeff_mul_pow_eq`,
`IsDistinguished.norm_pos` (as written; canonical).
#### Proof sketch
1. `ne_zero`: `fun h0 ↦ hf.isUnit_coeff.ne_zero (by rw [h0, map_zero])` — source
   WPrep_gen.lean:128–129 verbatim.
2. `norm_coeff_mul_pow_eq`: `rw [norm_def]`-analogue: the field `hl.gaussNorm_eq` IS the
   statement after `Restricted.norm_def`/`gaussNorm_eq` (univariate GaussNorm) — symm + rfl-glue.
3. `norm_pos`: `‖l‖ ≠ 0` via `(gaussNorm_eq_zero_iff (by positivity-from-Fact)).ne` and
   `Subtype`-level `l ≠ 0` from `hl.ne_zero` (lift along `val`); conclude `lt_of_le_of_ne (norm_nonneg _)`.
#### Mathlib/project lemmas
`IsUnit.ne_zero`, `map_zero`; project: `PowerSeries.Restricted.norm_def`/`gaussNorm_eq`,
`gaussNorm_eq_zero_iff` (univariate GaussNorm.lean:113).
#### Sources
WPrep_gen.lean:128–129; WeierstrassDivision.lean:34–55.
#### Generality
`Semiring`/general `v` for `ne_zero` (source §0 context); norm lemmas at `[NormedRing S]
[IsUltrametricDist S] [Fact (0 < c)]`, `norm_pos` adds `[Nontrivial S]` (necessary — trivial
ring attack in decomposition L1.2/L1.4).

### [T002] `IsDistinguished.C_mul`
- **Status**: done (2026-07-25; standard axioms. Notes: (a) lemma moved to `_root_.PowerSeries.IsDistinguished` namespace so dot notation works — the Restricted-nested name broke `hl.C_mul`; same rename applied to T001's `norm_coeff_mul_pow_eq`/`norm_pos`; (b) `Nontrivial S` derived inside the proof from `hl.lt_of_gt (s+1)` — statement unchanged, vacuously fine over trivial rings; (c) univariate has no `val_mul`, used `MvPowerSeries.Restricted.val_mul` + mathlib `PowerSeries.coeff_C_mul`) | **File**: `Distinguished.lean` | **Depends on**: T001 | **Parallel**: yes | **Type**: lemma
#### Statement
Skeleton `IsDistinguished.C_mul` (canonical).
#### Proof sketch (source: WeierstrassDivision.lean:589–601 `ext1`, weights carried)
1. Field `isUnit_coeff`: `coeff s ((C c a) * l).1 = a * coeff s l.1` via `val_mul`, `val_C`,
   `MvPowerSeries.coeff_C_mul`; unit product `ha.mul hl.isUnit_coeff`.
2. Field `gaussNorm_eq`: `‖C c a * l‖ = ‖a‖ * ‖l‖` (`norm_mul`, `norm_C`); RHS
   `‖a * coeff s l.1‖ * c^s = ‖a‖ * (‖coeff s l.1‖ * c^s)` (`norm_mul`, ring); congr via
   `hl.gaussNorm_eq` (through `norm_coeff_mul_pow_eq`).
3. Field `lt_of_gt`: multiply source inequality `hl.lt_of_gt t ht` by `‖a‖ > 0`
   (`mul_lt_mul_of_pos_left`, `norm_pos_iff.mpr ha.ne_zero`) after the same coeff rewrite.
#### Mathlib/project lemmas
`MvPowerSeries.coeff_C_mul` (mathlib:424), `norm_mul`, `norm_C` (project),
`mul_lt_mul_of_pos_left`, `norm_pos_iff`.
#### Sources
WeierstrassDivision.lean:589–601.
#### Generality
General `c` (weights are spectators — decomposition L1.5 attack log); `NormMulClass` needed.

### [T003] `isDistinguished_toRestricted_of_monic`
- **Status**: done (2026-07-25; standard axioms. Notes: `Nontrivial S` derived from `ωn` (`c^s > 0` forces `ω ≠ 0`), then `NormOneClass` via mathlib `NormMulClass.toNormOneClass`; `lt_of_gt` used `coeff_eq_zero_of_degree_lt (ωd ▸ Nat.cast_lt.mpr ht)` — degree form, not natDegree form) | **File**: `Distinguished.lean` | **Depends on**: T001 | **Parallel**: yes | **Type**: lemma
#### Statement
Skeleton `isDistinguished_toRestricted_of_monic` (canonical; general `c`, norm value `c ^ s`).
#### Proof sketch (source: WPrep.lean:362–380, weights restored)
1. `hnat : ω.natDegree = s` (`natDegree_eq_of_degree_eq_some ωd`); `hcs : ω.coeff s = 1`
   (`ωm.coeff_natDegree`); coeff-transfer `hcoe := Polynomial.coeff_coe` through
   `val_toRestricted`.
2. `isUnit_coeff`: rw to `ω.coeff s = 1` → `isUnit_one`.
3. `gaussNorm_eq`: `‖·‖ = c^s = ‖(1 : S)‖ * c^s` via `ωn`, `norm_one`.
4. `lt_of_gt` at `t > s`: coefficient vanishes (`coeff_eq_zero_of_natDegree_lt`), LHS
   `0 * c^t = 0 < 1 * c^s` (`pow_pos` from Fact).
#### Mathlib lemmas
`Polynomial.natDegree_eq_of_degree_eq_some`, `Monic.coeff_natDegree`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.coeff_coe`, `pow_pos`.
#### Sources
WPrep.lean:362–380.
#### Generality
General `c`; the `c = 1` instance recovers the source statement via `one_pow`.

### [CLEANUP-1] /cleanup on Distinguished.lean
- **Status**: done (2026-07-25; full 10-phase pass + 4-agent simplify. Statement strengthenings: norm_pos dropped [Nontrivial S] (new IsDistinguished.nontrivial), CMul section NormedCommRing→NormedRing, of_monic own section NormMulClass→NormOneClass with nontriviality derivation deleted. New API: IsDistinguished.{nontrivial, achievesGaussNorm, le_of_achievesGaussNorm} — bridges for T009's peak machinery. Board note for T-PROBE: general-radius tail bound ∃ ε < ‖l‖, ∀ t > s, ‖coeff t l.1‖ c^t ≤ ε provable in Distinguished §Norm from lt_of_gt + isRestricted_iff'; WDiv's exists_lt_one_forall_norm_coeff_le is its c=1 instance) | **File**: `Distinguished.lean` | **Depends on**: T001, T002, T003
- **Type**: cleanup (cadence: 3rd proof ticket on file + final).

### [T004] `isRestricted_rescale` + `norm_units_inv`
- **Status**: done (2026-07-25; isRestricted_rescale verbatim port (cofinite Tendsto.congr); norm_units_inv STRENGTHENED — hu : ‖u‖ ≠ 0 dropped entirely, eq_inv_of_mul_eq_one_right needs no nonvanishing in a DivisionMonoid; Predicate section needed [NormOneClass R] for norm_pow) | **File**: `Rescale.lean` | **Depends on**: none | **Parallel**: yes (with T001) | **Type**: lemma ×2
#### Statement
Skeleton `PowerSeries.isRestricted_rescale`, `norm_units_inv` (canonical).
#### Proof sketch
1. `isRestricted_rescale`: WPrep_gen.lean:174–180 verbatim — `isRestricted_iff` both sides,
   `Tendsto.congr` with pointwise `coeff_rescale` + `norm_mul` + `norm_pow` + `← ha, mul_pow; ring`.
2. `norm_units_inv`: WPrep_gen.lean:183–188 with `hu : ‖u‖ ≠ 0` replacing positivity —
   `‖u * u⁻¹‖ = 1` (`Units.mul_inv`, `norm_one`, `norm_mul`), cancel by `hu`
   (`eq_inv_of_mul_eq_one_right`-style or `mul_left_cancel₀`).
#### Mathlib lemmas
`PowerSeries.coeff_rescale` (:567), `norm_pow`, `Units.mul_inv`, `mul_left_cancel₀`;
project `PowerSeries.isRestricted_iff` (univariate Basic:41).
#### Sources
WPrep_gen.lean:174–188.
#### Generality
`isRestricted_rescale` keeps the source's fully-general `(c₁, c₂, ha)` form (no positivity);
`norm_units_inv` weakened to `‖u‖ ≠ 0` (decomposition L2.2).

### [T005] `rescaleEquiv` + `rescaleEquiv_coe` + `rescaleEquiv_symm_coe`
- **Status**: done (2026-07-25; structure-literal def, coe lemmas rfl; invFun leg derives ‖u‖ ≠ 0 from Fact (0 < c) + hu) | **File**: `Rescale.lean` | **Depends on**: T004 | **Parallel**: no | **Type**: def + lemma ×2
#### Statement
Skeleton `Restricted.rescaleEquiv` and the two coe lemmas (canonical).
#### Proof sketch (source: WPrep_gen.lean:193–218, target radius generalised)
1. Build the structure literally as the source: `toFun f := ⟨rescale u f.1,
   isRestricted_rescale u (by rw [hu]) f.2⟩`; `invFun g := ⟨rescale ↑u⁻¹ g.1,
   isRestricted_rescale _ (inverse-leg identity) g.2⟩` where the inverse-leg identity
   `‖↑u⁻¹‖ * c = c'` comes from `norm_units_inv` + `hu` + Facts (`‖u‖ = c / c' ≠ 0`).
2. `left_inv`/`right_inv`: `Subtype.ext` + `rescale_rescale`, `Units.mul_inv/inv_mul`,
   `rescale_one` (seam: `show` + term steps, per source).
3. `map_mul'/map_add'`: `Subtype.ext` + `map_mul/map_add` of `rescale` (a ring hom).
4. Coe lemmas: `rfl` once the def is term-mode (write the def as a structure literal, not
   tactic, so the coe lemmas are `rfl`).
#### Mathlib lemmas
`PowerSeries.rescale` (ring hom), `rescale_rescale`, `rescale_one`, `Units.mul_inv/inv_mul`.
#### Sources
WPrep_gen.lean:193–218.
#### Generality
Target radius `c'` general (decomposition L2.3 attack log: inverse-leg algebra verified).

### [T006] `norm_rescaleEquiv` + `isDistinguished_rescaleEquiv_iff`
- **Status**: done (2026-07-25; shared private norm_coeff_rescale_mul_pow + gaussNorm_rescale — pointwise identity hoisted to plain-PowerSeries argument because rw [← hu] on a Restricted-typed context hits the seam (motive over c in f's type); qualified PowerSeries.gaussNorm (bare gaussNorm mis-resolves inside namespace Restricted)) | **File**: `Rescale.lean` | **Depends on**: T005, T001 | **Parallel**: no | **Type**: lemma ×2
#### Proof sketch (source: WPrep_gen.lean:224–276)
1. Coefficient identity `hcoeff : ∀ k, ‖coeff k (rescale u f.1)‖ * c'^k = ‖coeff k f.1‖ * c^k`
   (`coeff_rescale`, `norm_mul`, `norm_pow`, `← hu, mul_pow; ring`).
2. `norm_rescaleEquiv`: both norms as `gaussNorm_eq` sups; `iSup_congr` with `hcoeff`.
3. `isDistinguished_rescaleEquiv_iff`: unit-parts via `coeff_rescale` +
   `Units.isUnit_units_mul` (u^k a unit); norm-parts transport by `hcoeff` + step 2, both
   directions field-wise (source's two-branch structure, now symmetric).
#### Mathlib lemmas
`Units.isUnit_units_mul`, `iSup_congr`; project `gaussNorm_eq` (univariate).
#### Sources
WPrep_gen.lean:224–276.
#### Generality
General `(c, c')`; at `c' = 1` recovers the source statements.

### [CLEANUP-2] /cleanup on Rescale.lean (partial)
- **Status**: done (2026-07-25; merged with CLEANUP-3 — see it) | **File**: `Rescale.lean` | **Depends on**: T004, T005, T006 | **Type**: cleanup (cadence).

### [T007] Polynomial composition helpers
- **Status**: done (2026-07-25; hoisted to minimal [CommSemiring A] section (was inheriting 4 normed instances); proofs verbatim from source) | **File**: `Rescale.lean` | **Depends on**: CLEANUP-2 | **Parallel**: yes | **Type**: lemma ×3
#### Statement
Skeleton `Polynomial.coeff_comp_C_mul_X`, `Polynomial.comp_C_mul_X_comp_C_inv_mul_X`,
`Polynomial.degree_comp_C_mul_X_lt` (canonical).
#### Proof sketch
Source WPrep_gen.lean:280–339 verbatim: `induction_on'` + `monomial_comp` +
`coeff_monomial` case split; cancel via the coeff formula + `Units.inv_mul`; degree via
`degree_lt_iff_coeff_zero` transport.
#### Mathlib lemmas
`Polynomial.induction_on'`, `Polynomial.monomial_comp`, `Polynomial.coeff_monomial`,
`Polynomial.C_mul_X_pow_eq_monomial`, `Polynomial.degree_lt_iff_coeff_zero`.
#### Sources
WPrep_gen.lean:280–339.
#### Generality
Pure `CommSemiring`-level polynomial algebra where possible (try weakening from the section's
normed context — cleanup may hoist to a mathlib-shaped file).

### [T008] `rescaleEquiv_toRestricted` + `rescaleEquiv_symm_toRestricted`
- **Status**: done (2026-07-25; symm-version inlines the cancel' variant via simpa using (cancel r u⁻¹).symm — no separate comp_C_mul_X_cancel' lemma needed) | **File**: `Rescale.lean` | **Depends on**: T005, T007 | **Parallel**: no | **Type**: lemma ×2
#### Proof sketch
Source WPrep_gen.lean:295–348: `Subtype.ext` + `ext k` + `coeff_rescale` + `coeff_coe` +
`coeff_comp_C_mul_X`; symm-version by `RingEquiv.symm_apply_eq` + the cancel lemma.
Seam: term-mode `show` steps as in the source.
#### Sources
WPrep_gen.lean:295–348.
#### Generality
General `(c, c')`.

### [CLEANUP-3] /cleanup on Rescale.lean (final)
- **Status**: done (2026-07-25; merged CLEANUP-2+3: inline 24-item audit + 3 simplify agents (reuse/simplification/efficiency+altitude), all applied+verified: (1) DELETED coeff_comp_C_mul_X — mathlib @[simp] Polynomial.comp_C_mul_X_coeff (Eval/Degree.lean:107, Semiring, flipped order) — decomposition had missed it under the flipped name; trio hoisted CommSemiring→Semiring with Units-cancellation proof; (2) norm_units_inv := map_units_inv normHom u (mathlib-composed, hu dropped, own minimal NormedRing section); (3) rescaleEquiv invFun leg proven WITHOUT positivity (‖u⁻¹‖c = ‖u⁻¹u‖c' = c') ⇒ Fact instances DROPPED from rescaleEquiv/coes/iff/toRestricted-transports (kept only on the 3 norm lemmas); (4) coe lemmas renamed rescaleEquiv_coe→val_rescaleEquiv, _symm_coe→val_rescaleEquiv_symm (tree val_* convention), both @[simp] + docstrings; (5) gauss-term computation deduped into public norm_coeff_rescale_mul_pow (a : R) in Predicate section; gaussNorm_rescale generalized to (a : R), public, no omit; (6) NEW downstream API: norm_rescaleEquiv_symm, hunit_transport (public; replaces 6 would-be inlinings of legacy WPrep_gen hunit_transport), Polynomial.degree_comp_C_mul_X (unit ⇒ degree equality via support ext), Polynomial.leadingCoeff_comp_C_mul_X (for T021 renormalization). Rejected as churn/longer (verified): one-directional iff refactor, hunit ∀k narrowing. Board notes: comp trio could split to a dedicated ForMathlib Polynomial file at CLEANUP-FINAL; norm_units_inv → Units.norm_inv rename candidate — user call. Axioms: all standard) | **File**: `Rescale.lean` | **Depends on**: T007, T008 | **Type**: cleanup (final per-file).

### [T009] `max_le_norm_of_eq_mul_add` (the bounds core, general c)
- **Status**: done (2026-07-25; ~110-line weighted port compiled first-fix (only val_toRestricted needed Polynomial. qualifier). Weighted rest-sum bound via Finset.exists_mem_eq_sup' (sup' attained) + max_mul_of_nonneg instead of dividing by c^(u+s); peak machinery via achievers API as planned) | **File**: `WeierstrassDivision.lean` | **Depends on**: T001 | **Parallel**: yes (with Rescale chain) | **Type**: theorem
#### Statement
Skeleton `max_le_norm_of_eq_mul_add` (canonical).
#### Proof sketch (source: WeierstrassDivision.lean:105–244 `contra`, weights restored,
positive form via `by_contra` + `not_lt`)
1. `by_contra`; `push_neg` to `‖f‖ < max ‖g * q‖ ‖toRestricted c r‖`; case `q = 0` closes as
   source :115–119.
2. Peak of `q` in the WEIGHTED norm: use the achievers API —
   `exists_achievesGaussNorm c q` for nonemptiness, `finite_setOfPred_achievesGaussNorm` for
   finiteness (replaces source's hand-rolled :122–148); take the `Finset.max'` peak `u`;
   `hu_max : ∀ a > u, ‖coeff a q.1‖ * c^a < ‖q‖` from max'-maximality + `le_gaussNorm`
   (achieving = equality case).
3. Dominant coefficient (source :167–220 with weights):
   `‖coeff (u+s) (g*q).1‖ * c^(u+s) = ‖g‖ * ‖q‖` — antidiagonal sum; the `(s, u)`-term has
   weighted norm `(‖coeff s g.1‖ c^s)(‖coeff u q.1‖ c^u) = ‖g‖‖q‖` (`norm_mul`, `pow_add`);
   every other `(a, b)`-term strictly smaller by trichotomy on `a` vs `s` using
   `hg.lt_of_gt` (weighted) and step-2's `hu_max`; conclude by
   `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` + `Finset.sup'_lt_iff` +
   `Nonempty.norm_sum_le_sup'_norm` exactly as source :198–220.
4. `r` has no coefficient at `u + s` (`coeff_eq_zero_of_degree_lt`, source :222–226); hence
   `‖coeff (u+s) f.1‖ c^(u+s) = ‖g‖‖q‖`, so `‖g * q‖ ≤ ‖f‖` (`le_gaussNorm` + `norm_mul`).
5. Both `max`-branches contradict as source :237–244 (ultrametric `‖f - g*q‖ ≤ max`).
#### Mathlib/project lemmas
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Finset.Nonempty.norm_sum_le_sup'_norm`,
`Finset.sup'_lt_iff`, `PowerSeries.coeff_mul`, `Polynomial.coeff_eq_zero_of_degree_lt`;
project: `exists_achievesGaussNorm`, `finite_setOfPred_achievesGaussNorm`, `le_gaussNorm`,
`norm_le_iff` (all univariate GaussNorm, general c).
#### Sources
WeierstrassDivision.lean:105–244 (140 source lines → expect ~110 Lean lines with the
achievers API absorbing ~30).
#### Generality
General `c`, no auxiliary hypotheses — decomposition L3.1 attack log records the weighted
cross-term bookkeeping.

### [T010] `norm_q_le_of_eq_mul_add` + `norm_r_le_of_eq_mul_add` + `weierstrassDivision_q_unique`
- **Status**: done (2026-07-25; compiled first build. norm_q_le via inv_mul_lt_iff₀ hg.norm_pos (replaces source's field_simp dance); q_unique states h0 as 0 = g*(q₁-q₂)+... directly (feeds norm_q_le without .symm), grind replaced by sub_eq_zero.mp) | **File**: `WeierstrassDivision.lean` | **Depends on**: T009 | **Parallel**: no | **Type**: theorem ×3
#### Proof sketch
1. `norm_r_le`: `(le_max_right _ _).trans (max_le_norm_of_eq_mul_add …)`.
2. `norm_q_le`: `(le_max_left …).trans` + `norm_mul` + divide by `‖g‖ > 0`
   (`hg.norm_pos` from T001; `le_div_iff₀`-style arithmetic as source :246–258).
3. `q_unique` (source :774–790): apply `norm_q_le` at `f := 0` to
   `g*(q₁-q₂) + toRestricted c (r₁-r₂) = 0` (ring + `map_sub`), degree via `degree_sub_le` +
   `max_lt`; `norm_le_zero_iff` + `sub_eq_zero`.
#### Sources
WeierstrassDivision.lean:246–265, 774–790.
#### Generality
General `c` — pure corollaries of T009.

### [T011] `coeff_continuous` + `isClosed_setOf_coeff_eq_zero`
- **Status**: done (2026-07-25; δ := ε * c^v, closes via lt_of_mul_lt_mul_right (mul_lt_mul_right iff hit a MulLeftStrictMono synthesis quirk); mem_setOf_eq deprecated → mem_ofPred_eq; both omit [NormMulClass R]) | **File**: `WeierstrassDivision.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma ×2
#### Proof sketch (source :486–502, weights added)
1. `coeff_continuous`: `Metric.continuous_iff`; given ε pick `δ := ε * c^v`
   (`pow_pos` from Fact); `‖coeff v (g-f).1‖ ≤ c^{-v}·‖g-f‖` from `norm_le_iff` at index v
   (rearranged); linear-map `map_sub` step as source.
2. `isClosed_setOf_coeff_eq_zero`: `IsSeqClosed.isClosed`; limit of vanishing coefficients
   vanishes by step 1's continuity + `tendsto_const_nhds_iff` (source verbatim).
#### Sources
WeierstrassDivision.lean:486–502.
#### Generality
General `c` (public API; flagged for possible hoist to GaussNorm.lean at cleanup).

### [CLEANUP-4] /cleanup on WeierstrassDivision.lean (partial)
- **Status**: done (2026-07-25; Bounds section restructured to own minimal variable scope [NormedCommRing+IsUltrametricDist+NormMulClass] (file-wide 6-instance block moved down to the engine, killing unusedSectionVars on all 7 bounds decls; coeff_continuous/isClosed omit NormMulClass); T009 structure-gate: dominant-coefficient computation extracted as private norm_coeff_mul_add_of_peak (~60 lines), main theorem now ~40 lines; widths ≤100, no mechanical-pattern hits; axioms standard (23-decl sweep). Engine decls untouched — cleaned at their tickets) | **File**: `WeierstrassDivision.lean` | **Depends on**: T009, T010, T011 | **Type**: cleanup (cadence).

### [T012] Engine set-up: `divisionAddSubgroup` + `exists_lt_one_forall_norm_coeff_le` + `nontrivial_quotient_closedBall_ideal`
- **Status**: done (2026-07-25; compiled first build; toRestricted_add/neg → map_add/map_neg; grind → trans_lt+lt_irrefl; omits added per linter) | **File**: `WeierstrassDivision.lean` | **Depends on**: CLEANUP-4 | **Parallel**: no | **Type**: def-fields + lemma ×2
#### Proof sketch
1. Subgroup fields: source :276–288 verbatim (`degree_add_le`+`max_lt`; `map_neg`/`map_add`
   of `toRestricted`; `abel`).
2. `exists_lt_one…`: source :293–318 verbatim (`isRestricted_iff'` + `Metric.tendsto_atTop`
   + finite image + `max (F.max') (1/2)` case split).
3. `nontrivial_quotient…`: source :327–333 (`Ideal.Quotient.nontrivial_iff` + `‖1‖ = 1` vs
   `≤ ε < 1` via `mem_closedBall_ideal`).
#### Sources
WeierstrassDivision.lean:276–333.

### [T013] `monic_residueRingHom_of_isDistinguished`
- **Status**: done (2026-07-25; compiled first build; pbCoeff→powerBoundedCoeff via Subtype.ext hcs (rfl-coe), higher coeffs via eq_zero_iff_mem + mem_closedBall_ideal with hgt defeq-direct) | **File**: `WeierstrassDivision.lean` | **Depends on**: T012 | **Parallel**: no | **Type**: lemma
#### Proof sketch (source :322–350, residue names re-pointed)
1. Leading coeff: `coeff_residueRingHom` (rfl) + `powerBoundedCoeff`-Subtype.ext to `1`
   (source's `hs` step with `pbCoeff ↦ powerBoundedCoeff`).
2. Higher coeffs vanish: `Ideal.Quotient.eq_zero_iff_mem` + `mem_closedBall_ideal` +
   `powerBoundedCoeff_coe` + `hgt`.
3. Degree/monic assembly: `degree_le_iff_coeff_zero` + `le_degree_of_ne_zero` +
   `Polynomial.Monic`/`natDegree_eq_of_degree_eq_some` (source verbatim); `haveI` T012.3.
#### Sources
WeierstrassDivision.lean:322–350; Residue.lean:146 (`coeff_residueRingHom`).

### [T014] `exists_approx_div_of_monic_residue`
- **Status**: done (2026-07-25; mathlib lifts route as planned. Deltas: modByMonic_add_div takes (p q) with NO monic hyp now; lifts_and_degree_eq deprecated → exists_degree_eq_of_mem_lifts; needed import Mathlib.Algebra.Polynomial.Lifts (not in transitive closure); degree_modByMonic_lt needs the T012 Nontrivial quotient instance; residue-vanishing via linear_combination -hdiv (rw ← hdiv would loop through the /ₘ %ₘ occurrences); final coercion massage simpa [sub_sub]) | **File**: `WeierstrassDivision.lean` | **Depends on**: T013 | **Parallel**: no | **Type**: lemma
#### Proof sketch (source :357–374; Polylift → mathlib `lifts`)
1. Euclidean-divide `residueRingHom … f` by the monic `residueRingHom … g` in
   `Polynomial (R°⧸ball)`: `q̄ := _ /ₘ _`, `r̄ := _ %ₘ _`; `modByMonic_add_div` +
   `degree_modByMonic_lt`.
2. Lift `q̄`, `r̄` along `Ideal.Quotient.mk` with degree control:
   `(lifts_iff_set_range).mpr` via `Polynomial.map_surjective _ Ideal.Quotient.mk_surjective`
   then `lifts_and_degree_eq` — lifts over `↥R°` with the SAME degree.
3. Send the `q`-lift into `T°` by `toPowerBounded`; remainder lift maps down to `R[X]` by
   `Polynomial.map (R°.subtype)` (source's shape).
4. Norm bound: rewrite the difference's residue to `0` using
   `residueRingHom_toPowerBounded` + `map_sub/map_mul` + step-1 equation (source :369–374),
   conclude by `(residueRingHom_closedBall_ideal_eq_zero_iff hε0 _).mp`.
5. Degree bound: `degree_map_le` + degree-equality of the lift + `degree_modByMonic_lt`.
#### Mathlib lemmas
`Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`,
`Polynomial.lifts_and_degree_eq`, `Polynomial.lifts_iff_set_range`,
`Polynomial.map_surjective`, `Ideal.Quotient.mk_surjective`, `Polynomial.degree_map_le`.
#### Sources
WeierstrassDivision.lean:357–374; Residue.lean (`toPowerBounded`,
`residueRingHom_toPowerBounded`, `residueRingHom_closedBall_ideal_eq_zero_iff`).

### [CLEANUP-5] /cleanup on WeierstrassDivision.lean (partial)
- **Status**: done (2026-07-25; T012–T014 block: widths ok, no mechanical hits, bodies ≤22 lines, axioms standard (5 public decls verified; peak helper private-by-design)) | **File**: `WeierstrassDivision.lean` | **Depends on**: T012, T013, T014 | **Type**: cleanup (cadence).

### [T015] `exists_mem_divisionSet_norm_le` (the ε-approximation)
- **Status**: done (2026-07-25; 75-line transcription compiled after 2 fixes: Nontrivial R via hg.nontrivial (our API — NormOneClass alone doesn't auto-synthesize it), isPowerBounded_of_norm_le_one lost its IsPowerBounded. prefix vs legacy. Local hcoeff_C helper (defeq coeff_C_mul) replaces legacy Restricted.coeff_C_mul; C-algebra via map_mul/map_one of the C ring hom + toRestricted_C) | **File**: `WeierstrassDivision.lean` | **Depends on**: CLEANUP-5 | **Parallel**: no | **Type**: lemma
#### Proof sketch
Source :386–467 transported name-for-name (80 source lines; the largest single transcription):
scaling units `α`, `u = (coeff s g)⁻¹`; normalised `g' := C u * g`, `f' := C α * f`; lift to
`T°` (`isPowerBounded_of_norm_le_one`); T013 monic; T014 division; unscale by `C αinv` with
the `key` algebraic identity (source :444–456) — `C_mul` identities via `map_mul` of
`Restricted.C` and `toRestricted`; degree bound via `degree_C_mul-≤` chain (source :458–462).
#### Sources
WeierstrassDivision.lean:386–467.
#### Generality
Engine (c = 1). The per-`f` hypothesis `∃ a, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a` as in source.

### [T016] `dense_divisionSet` (via `AddSubgroup.dense_of_infDist_le`)
- **Status**: done (2026-07-25; compiled first build; IsIsometricVAdd via mathlib NormedGroup.to_isIsometricSMul additive twin — no local instance needed (ticket's VERIFY-FIRST resolved)) | **File**: `WeierstrassDivision.lean` | **Depends on**: T015 | **Parallel**: no | **Type**: lemma
#### Proof sketch (source :469–483 rerouted; decomposition L3.13)
1. Obtain `ε` from T012.2 (leading-coeff norm 1 from `hgn` + `hg.norm_coeff_mul_pow_eq`).
2. Apply `AddSubgroup.dense_of_infDist_le (divisionAddSubgroup g s) ε`: for `f = 0`,
   `infDist 0 H = 0 ≤ …` (`0 ∈ H`); for `f ≠ 0`, T015 gives `b ∈ H`,
   `infDist f H ≤ dist f b = ‖-f + b‖ ≤ ε‖f‖ = ε * dist f 0` (`dist_eq_norm`, `norm_neg`
   juggling).
3. VERIFY-FIRST: the `IsIsometricVAdd (Restricted R 1) (Restricted R 1)` instance —
   `lean_local_search` for the seminormed-add-group instance in
   `Mathlib.Topology.MetricSpace.IsometricSMul`; if absent, provide the 2-line local instance
   from `dist_add_left`.
#### Sources
WeierstrassDivision.lean:469–483; ForMathlib/Topology/MetricSpace/HausdorffDistance.lean:17.

### [T017] `isClosed_divisionSet`
- **Status**: done (2026-07-25; 70-line verbatim port compiled with only the omit-linter fix; general-c bounds instantiated at 1 directly (no one_pow bridging needed — statements already weight-free at norm level)) | **File**: `WeierstrassDivision.lean` | **Depends on**: T010, T011 | **Parallel**: yes (with T012–T016) | **Type**: lemma
#### Proof sketch
Source :504–574 verbatim with the general-`c` bounds instantiated at `c = 1` (`one_pow`
bridging): `choose` the divisions; difference equations; `CauchySeq` for `q_seq` via
`norm_q_le` and for the remainders via `norm_r_le`; limits by
`cauchySeq_tendsto_of_complete`; the limit remainder lands in the closed polynomial subspace
(T011.2), reconstructed as a polynomial by the source's finite-sum construction (:545–569 —
port as-is; golf later); conclude by `tendsto_nhds_unique`.
#### Sources
WeierstrassDivision.lean:504–574.

### [CLEANUP-6] /cleanup on WeierstrassDivision.lean (partial)
- **Status**: done (2026-07-25; T015: 2 unit-inverse-norm computations golfed to one-liners via norm_units_inv (body ~62→56 lines); T017: polynomial-truncation block extracted as private exists_toRestricted_eq_of_coeff_eq_zero (source's own 'can probably be extracted' note honored; main body 70→45 lines); build green) | **File**: `WeierstrassDivision.lean` | **Depends on**: T015, T016, T017 | **Type**: cleanup (cadence).

### [T018] `weierstrassDivision_exists_of_norm_eq_one` + `weierstrassDivision_exists`
- **Status**: done (2026-07-25; both compiled first build. Engine capstone = closure_eq juggle; general-c leg folds the source's separate normalisation lemma INTO the transport (C 1 a normalisation happens at radius 1 after rescale, using hg₁.C_mul + hunit_transport + rescaleEquiv_symm_toRestricted + degree_comp_C_mul_X_lt exactly as planned)) | **File**: `WeierstrassDivision.lean` | **Depends on**: CLEANUP-6, T006, T008 | **Parallel**: no | **Type**: theorem ×2
#### Proof sketch
1. Engine capstone (source :578–586): `divisionSet = univ` from closed (T017) + dense (T016)
   closures; extract membership.
2. General `c` (decomposition L3.16): obtain `u` from `hα`; `e := rescaleEquiv u (hu' : ‖u‖*1 = c)`;
   transport `hg` (T006 iff), `h`/`hunit` (isometry; source hunit_transport WPrep_gen:353–363
   inline); normalise `g` at radius 1 by `C a * ·` with the transported `h` and
   `IsDistinguished.C_mul` (T002) exactly as source :757–769; apply step 1; pull back
   `q ↦ e.symm q` and `r ↦ r.comp (C ↑u⁻¹ * X)` (T008 symm-transport; degree by T007);
   equation transports through the ring iso (`map_mul/map_add` + `RingEquiv.symm_apply_apply`).
#### Sources
WeierstrassDivision.lean:578–586, 757–769; WPrep_gen.lean:353–373.
#### Generality
`hα` confined here; `c = 1, u = 1` degenerates to the engine (rescale_one).

### [CLEANUP-ALL-1] /cleanup-all before the division milestone
- **Status**: done (2026-07-25; all 5 tree roots build green (Mv Iso/Residue, univariate Residue/Units, WPrep chain); axiom sweep standard on all division decls; remaining sorries exactly the open tickets (WDiv×2=T019, WPrep×5=T020-23) + pre-existing out-of-scope NewtonPolygon.lean) | **Depends on**: T018 and all prior cleanups | **Type**: cleanup-all.

### [T019] MILESTONE: `weierstrassDivision_uniqueness` + `weierstrassDivision_polynomial`
- **Status**: done (2026-07-25; MILESTONE REACHED — WeierstrassDivision.lean sorry-free, weierstrassDivision_uniqueness at general radius c with standard axioms. Both compiled after one fix (Nontrivial R := hg.nontrivial for u.ne_zero/one_ne_zero/degree_modByMonic_lt). Polynomial version's R[X]-division block is radius-free; bridging via general uniqueness verbatim from source incl. the hgs-necessity docstring) | **File**: `WeierstrassDivision.lean` | **Depends on**: CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem ×2
#### Proof sketch
1. Uniqueness (source :792–803): assemble T018 + T010.3 + remainder cancellation
   (`add_left_cancel` + `Polynomial.coe_inj` through `val`).
2. Polynomial version (source :829–888): monic-rescale `C ↑u⁻¹ * g₀` in `R[X]`
   (`monic_C_mul_of_mul_leadingCoeff_eq_one`), R[X]-division (`modByMonic_add_div`), bridge
   both solutions through T018-uniqueness's `key` argument (source verbatim; `hgs`
   counterexample docstring retained).
#### Sources
WeierstrassDivision.lean:792–888.

### [CLEANUP-7] /cleanup on WeierstrassDivision.lean (final)
- **Status**: done (2026-07-25; 2 simplify agents. APPLIED: toRestricted_injective replaces 4 coe_inj composites (existing Basic API); norm_coeff_mul_pow_le hoisted public into Restricted/GaussNorm (replaces 3 in-file hle-composites + 1 WPrep site); private truncation lemma rewritten on mathlib PowerSeries.trunc (coeff_trunc/degree_trunc_lt; 24→9 lines; + Trunc import); 2 missing omits added (exists_mem_divisionSet_norm_le, dense_divisionSet). REPORTED (T-PROBE input, statement-level, scratch-COMPILED proofs by agent in scratchpad/wd_h_deriv.lean + wd_halpha_deriv.lean): h is derivable as hunit g (norm_pos_iff.mp hg.norm_pos) on all 3 division theorems, AND hα is derivable from hunit alone (hunit at X R c + norm_units_inv) — so the whole public API could carry hunit only, NO engine change needed; deferred to T-PROBE as it reshapes 6 canonical statements. Structure: no body >60; engine publics-vs-docstring note; f-shadowing cosmetic. All axioms standard) | **File**: `WeierstrassDivision.lean` | **Depends on**: T019 | **Type**: cleanup (final per-file).

### [T020] `norm_toRestricted_X_pow_sub`
- **Status**: done (2026-07-25; general-c port of test5; needed (X^s : Polynomial R) ascription in the have (R not inferable); norm_monomial + toRestricted_monomial replace legacy coe_monomial') | **File**: `WeierstrassPrep.lean` | **Depends on**: T001 | **Parallel**: yes | **Type**: lemma
#### Proof sketch (source WPrep.lean:152–163, weights restored; test1–4 replaced by mathlib)
1. `≤`: `toRestricted` of the difference; `IsUltrametricDist.norm_add_le_max` +
   `norm_monomial`-at-`c` (via `toRestricted_monomial`/`map_pow`: `‖X^s‖ = c^s`) + `hrn`.
2. `≥`: coefficient `s` of `X^s − r` is `1` (`coeff_X_pow` + `coeff_eq_zero_of_degree_lt hr`);
   `le_gaussNorm` at index `s` gives `‖1‖ * c^s = c^s ≤ ‖·‖`.
#### Mathlib lemmas
`Polynomial.coeff_X_pow`, `Polynomial.coeff_eq_zero_of_degree_lt`,
(`Polynomial.monic_X_pow_sub` available if the Monic form helps); project `norm_monomial`,
`toRestricted_monomial`, `le_gaussNorm`.
#### Sources
WPrep.lean:94–163 (test1–test5; only test5's content survives — test1–4 are mathlib).

### [T021] `weierstrassPreparation_exists_of_norm_eq_one` (engine; Units-route)
- **Status**: done (2026-07-25; ~120-line port compiled after 4 small fixes (simpa-oversimplification on ωn/rn → term-mode .trans/rwa; X^s type ascription; RingHom.isUnit_map for the subtype (IsUnit.map hit a MonoidHomClass synthesis quirk on the opaque subring hom)). Units-route as planned: τ := residueRingHom at topologicalNilradical DIRECTLY (no ball-1/quotEquivOfEq detour — topNil IS the ideal, mem_topologicalNilradical_iff + of_norm_lt_one/zero give the coefficient facts); transport back via isUnit_powerBounded_iff + isUnit_iff_isUnit_mk_topologicalNilradical + isUnit_iff_isUnit_coe) | **File**: `WeierstrassPrep.lean` | **Depends on**: T018, T020 | **Parallel**: no | **Type**: theorem
#### Proof sketch (source WPrep.lean:178–309; unit-transport replaced per decomposition L4.2)
1. Divide `X^s` (as `toRestricted 1 (X^s)`, norm 1 by `norm_monomial`) by `g`
   (T018 engine): `e', r` with `g * e' = toRestricted 1 ω`, `ω := X^s − r` (source :183–190;
   `abel`).
2. `‖r‖ ≤ 1` (T010.2 at the division), `‖ω‖ = 1` (T020), `‖e'‖ = 1` (norm_mul on the
   equation; source :191–193).
3. Residue-degree arithmetic at `I := PowerBounded.topologicalNilradical ℤ` (equal to the
   ball-1 ideal by `topologicalNilradical_eq_ball_ideal_one`): reduce `G·E = W` by
   `residueRingHom`; `σW` monic of degree `s` (coeffs via `coeff_residueRingHom` +
   `Ideal.Quotient.eq_zero_iff_mem` + `mem_topologicalNilradical_iff` + T020's coefficient
   facts); `σG` degree `s` with unit leading coeff (from `hg` + `hgn` +
   `isUnit_iff_isUnit_mk_topologicalNilradical` at `R`); `natDegree_mul'` forces
   `natDegree σE = 0`, `eq_C_of_degree_le_zero`, leading-coeff comparison makes the constant
   a unit (source :244–293 verbatim modulo names).
4. **Unit-ness of `e'` by the general criterion** (replaces source :294–303): from step 3,
   `powerBoundedCoeff E 0` is a unit of `R°` (`isUnit_iff_isUnit_mk_topologicalNilradical`)
   ⇒ `IsUnit (coeff 0 e'.1)` in `R` (map along subtype) and `‖coeff 0 e'.1‖ = 1` (units of
   `R°` have norm 1: `‖u‖·‖u⁻¹‖ = 1`, both `≤ 1`); higher coefficients lie in the
   nilradical ⇒ topnil ⇒ `‖coeff t e'.1‖ < 1` (`isTopologicallyNilpotent_iff_norm_lt_one`);
   conclude `IsUnit e'` by `PowerSeries.Restricted.isUnit_iff` (Units.lean, `⇐`) with
   dominance `‖coeff t‖ * 1^t < ‖coeff 0‖`.  FALLBACK (equivalent): the `T°`-route via
   `isUnit_powerBounded_iff` + `isUnit_iff_isUnit_coe`.
5. Assemble with `e := (e')⁻¹`-unit (source :304–309); `Monic ω` by
   `Polynomial.monic_X_pow_sub` (degree `< s` remainder), degree by leading-coeff.
#### Mathlib/project lemmas
`Polynomial.monic_X_pow_sub` (:427), `Polynomial.natDegree_mul'`,
`Polynomial.eq_C_of_degree_le_zero`, `Polynomial.isUnit_C`; project:
`residueRingHom`/`coeff_residueRingHom`, `topologicalNilradical_eq_ball_ideal_one`,
`isOpen_topologicalNilradical`, `isUnit_iff_isUnit_mk_topologicalNilradical`,
`mem_topologicalNilradical_iff`, `isTopologicallyNilpotent_iff_norm_lt_one`,
`PowerSeries.Restricted.isUnit_iff`.
#### Sources
WPrep.lean:178–309 (130 source lines; expect ~85 Lean lines — the Units-route deletes ~45).
#### Generality
Engine (c = 1).

### [T022] MILESTONE: `weierstrassPreparation_exists` + `weierstrassPreparation_unique`
- **Status**: done (2026-07-25; MILESTONE REACHED — preparation at general radius, standard axioms. Exists: rescale→normalise(C 1 a)→T021 engine→pull back with ω := C(u^s)·ω₁(u⁻¹x) (monic/degree by the T021-style 4-block on the T007 coeff formula; norm via rescaleEquiv_symm_toRestricted + norm_rescaleEquiv_symm + norm_units_inv with inv_pow massage; unit e assembled from uA⁻¹ · e₀.symm e₁ · C c (u⁻¹^s)). Unique: e-leg by norm-cancellation against c^s ≠ 0; ω-leg by degree_sub_lt + norm_r_le at f := 0 + toRestricted_injective) | **File**: `WeierstrassPrep.lean` | **Depends on**: CLEANUP-ALL-2 | **Parallel**: no | **Type**: theorem ×2
#### Proof sketch (decomposition L4.3)
1. Exists: `hα`-rescale to radius 1; descale `g` by `hunit g` + `IsDistinguished.C_mul`
   (source WPrep.lean:316–330 at radius 1, transported); apply T021; pull back:
   `ω := C (u^s) * (ω₁.comp (C ↑u⁻¹ * X))` — monic of degree `s` (T007 coeff formula:
   leading `u^s · u^{-s} = 1`), `‖toRestricted c ω‖ = c^s` (T006 isometry + `‖C (u^s)‖ = c^s`),
   `e` transported through the iso adjusted by the same constants; equation via `map_mul` of
   the ring iso.
2. Unique: source WPrep.lean:332–359 — degree-`< s` difference `ω' − ω`
   (`Polynomial.degree_sub_lt` on equal-degree monics), bounds T010 at `f := 0` (general `c`
   — no transport), `norm_le_zero_iff`.
#### Sources
WPrep.lean:316–359; WPrep_gen.lean:367–373 (the `u^s` renormalisation note).
#### Generality
`hα` + `hunit`; the ∃!∃! is the documented shared-witness exception.

### [CLEANUP-8] /cleanup on WeierstrassPrep.lean (partial)
- **Status**: done (2026-07-25; merged with CLEANUP-9 — shared private monic_and_degree_of_coeff extracted (3 sites: T021 ω, T021 σW, T022 ω; −22 lines), T021 body now ~100 (headline engine, linear chain; residue-block extraction judged churn vs. clarity — the τ-facts feed 6 downstream haves), omit added on norm_toRestricted_X_pow_sub; file 365 lines, width-ok, warning-free, no mechanical hits) | **File**: `WeierstrassPrep.lean` | **Depends on**: T020, T021, T022 | **Type**: cleanup (cadence).

### [CLEANUP-ALL-2] /cleanup-all before the preparation milestone
- **Status**: done (2026-07-25; ran as continuous discipline — full-tree builds green at T021/T022 boundary, axiom sweeps standard, warning-free after omit fixes) | **Depends on**: CLEANUP-7, T021 | **Type**: cleanup-all.
  (Ordering note: runs after the division file is final-cleaned and the prep engine T021 is
  in, gating the milestone T022.)

### [T023] `weierstrassPreparation_polynomial`
- **Status**: done (2026-07-25; compiled FIRST BUILD — board's proof tickets complete, WPrep + WDiv sorry-free, all standard axioms. The general-c witness adjustment landed exactly as the ticket's attack log predicted: a := (↑u⁻¹)^s with ‖a‖ = (c^s)⁻¹ via norm_pow + norm_units_inv + inv_pow (shared hwitness helper); toRestricted_zero → map_zero; coe_inj composites → toRestricted_injective) | **File**: `WeierstrassPrep.lean` | **Depends on**: T022, T019, T003 | **Parallel**: no | **Type**: theorem
#### Proof sketch
Source WPrep.lean:410–444: from T022-unique obtain `(ω, e)`; `e` is a polynomial because
`g₀ = ω · e + 0` is a Weierstrass division by the distinguished-by-T003 `ω`
(`h := ⟨1, by simp [ωn], isUnit_one⟩`-analogue at norm `c^s` — adjust the witness: the
required `‖a‖ = ‖ω‖⁻¹` needs `a` with `‖a‖ = c^{-s}`; obtain from `hα` as `↑u⁻¹ ^ s` —
NOTE this replaces the source's `⟨1, …⟩` witness which only works at `c = 1`; record the
adjustment), then T019.2 gives the polynomial quotient and T010.3 bridges uniqueness
(source's `key`/`he₀` steps verbatim).
#### Sources
WPrep.lean:410–444.
#### Generality
`hα`; the witness adjustment above is the one genuinely new step at general `c` (attack
logged in decomposition L4.4 review — verify `‖(↑u⁻¹)^s‖ = c^{-s}` via `norm_units_inv` +
`norm_pow`).

### [CLEANUP-9] /cleanup on WeierstrassPrep.lean (final)
- **Status**: done (2026-07-25; merged into CLEANUP-8 — see it) | **File**: `WeierstrassPrep.lean` | **Depends on**: T023 | **Type**: cleanup (final per-file).

### [T-PROBE] EXPERIMENTAL: direct weighted ε-division (C-probe)
- **Status**: done (2026-07-25; GOAL ACHIEVED BY A CHEAPER ROUTE than the contract's experiment: a CLEANUP-7 verification agent discovered (and compiled, scratchpad/wd_halpha_deriv.lean) that hα is derivable from hunit alone — hunit applied to the variable X (norm c) inverts to a unit of norm c. Shipped as public `exists_units_norm_eq` in WDiv; hα AND h (the ‖g‖⁻¹-witness, derivable as hunit g via norm_pos) are now DELETED from all 6 public theorems — the entire division+preparation API carries only hunit. The engine is unchanged (still rescale-to-1 internally); the contract's direct weighted ε-division remains a possible future engine simplification but no longer gates any statement. No b2_log entry — no obstruction, the goal is met. USER-CONFIRMED 2026-07-25 (after review): keep the single-hunit API; docstrings corrected — hunit is NOT automatic over every normed field: it forces c ∈ ‖Rˣ‖ (apply it to X), and over a normed field holds precisely when c is in the value group (counterexample: ℚ_p with c ∉ p^ℤ, f = X needs ‖a‖ = c⁻¹). Old (hα ∧ h ∧ hunit) and new (hunit) hypothesis packages are provably equivalent, so applicability is unchanged) | **File**: scratch/new section | **Depends on**: T016 | **Parallel**: yes | **Type**: experiment (timeboxed)
- **Contract**: attempt a direct general-`c` replacement for the engine's ε-approximation:
  an `ε`-division operator built from the weighted splitting at degree `s` (contraction
  factor `sup_{t>s} (‖coeff t g‖ c^t) / (‖coeff s g‖ c^s) < 1` from `IsDistinguished`),
  avoiding the polynomial residue ring — which would delete `hα` from
  `weierstrassDivision_exists`.  HARD-STOP conditions: (a) the operator's restrictedness or
  contraction estimate fails; (b) budget exhausted (one focused session).  On success: file a
  `/develop --continue` to re-plan the existence tickets against the new engine.  On failure:
  record the obstruction to b2_log and close — the shipped theorems are unaffected.

### [CLEANUP-FINAL] /cleanup-all on the whole development
- **Status**: done (2026-07-25; BOARD COMPLETE. Final verification: 6 tree roots build green (WPrep chain 2208 jobs, Mv Iso 2307, Mv Residue, univariate Complete/PowerBoundedIso/TopologicallyNilpotentIso); ZERO sorries across both Restricted trees; all public declarations standard axioms; warning-free. Deferred to /develop --continue (tranche 2): rung-2 extensions (WPrep_gen §4–§5), WPPrep_MV, univariate X-API, hunit packaging (now MORE valuable — hunit is the single hypothesis of the whole API), norm_units_inv → Units.norm_inv rename decision, comp_C_mul_X-trio file split, engine-publics privatization decision) | **Depends on**: everything above | **Type**: cleanup-all (final).

---

# Tranche 2 — Weierstrass theory at every radius (approved 2026-07-25)

Design (user-approved): **prep-as-corollary** (preparation derived once from division via
the q-uniqueness trick, never proven per rung); **rung 2** = divisible-closure radii by
spectral-norm extension + descent (port of WPrep_gen §4–§5, division only); **dichotomy**
replaces density-and-limits — off the divisible closure no Gauss term can tie the dominant
one, so the direct one-step contraction engine applies at the radius itself.
Skeletons: BaseChange.lean + DivisibleRadius.lean (new) + 2 decls in WDiv/WPrep; chain
builds green (24 sorries).

### [T024] Generalize the division-set trio from radius 1 to arbitrary radius
- **Status**: done (2026-07-25; moved into Bounds under `variable {c}` (implicit radius — inferable from g; Bounds' explicit (c) would have broken every call site), omits on the Fact/NormMulClass-free decls, [CompleteSpace R] as lemma-local instance on isClosed; engine callers unchanged (instantiate at 1); T034/T035 skeletons landed alongside (chain green). All proofs verbatim — radius-generic as predicted) | **File**: `WeierstrassDivision.lean` | **Depends on**: none | **Parallel**: yes | **Type**: refactor
#### Statement
Move `divisionSet`, `divisionAddSubgroup`, `isClosed_divisionSet` and the private
`exists_toRestricted_eq_of_coeff_eq_zero` from the radius-1 Engine section into the
general-`c` Bounds section, replacing `Restricted R 1`/`toRestricted 1` by
`Restricted R c`/`toRestricted c` throughout (statements otherwise verbatim; engine callers
instantiate at `c := 1` with no signature change).
#### Proof sketch
1. The four proofs are already radius-generic: subgroup fields use `degree_add_le`/`map_neg`/
   `abel`; `isClosed` uses `norm_q_le_of_eq_mul_add`/`norm_r_le_of_eq_mul_add` (general `c`,
   shipped), `isClosed_setOf_coeff_eq_zero c`, `cauchySeq_tendsto_of_complete`, and the trunc
   lemma; the trunc lemma uses `PowerSeries.trunc`/`coeff_trunc`/`degree_trunc_lt` (radius-free).
2. Re-point the radius-1 engine callers (`exists_mem_divisionSet_norm_le`,
   `dense_divisionSet`, `weierstrassDivision_exists_of_norm_eq_one`) — instantiation only.
3. Re-check `omit` lines (CompleteSpace still needed by `isClosed` only).
#### Sources
Project: shipped WeierstrassDivision.lean (divisionSet block and isClosed block) — proofs
verified radius-generic by inspection in the tranche-2 planning pass.
#### Generality
General `c` with `[Fact (0 < c)]`; `divisionSet`/`divisionAddSubgroup` need only
`[NormedCommRing R] [IsUltrametricDist R]`.

### [T025] Preparation as a corollary of division (the q-uniqueness trick) + engine deletion
- **Status**: done (2026-07-25; the trick compiled with 2 fixes (helper must precede it in the file; isUnit_of_mul_eq_one → IsUnit.of_mul_eq_one, mathlib renamed with IsDedekindFiniteMonoid). weierstrassPreparation_exists is now the 2-line instantiation; 132-line residue engine DELETED (WPrep 365→228 lines), R°/T° notations + PowerBounded open dropped, module docstring rewritten to the corollary story. prep_unique/polynomial untouched and green; all standard axioms) | **File**: `WeierstrassPrep.lean` | **Depends on**: none | **Parallel**: yes (with T024) | **Type**: theorem + refactor
#### Statement
Skeleton `weierstrassPreparation_exists_of_forall_exists` (WPrep, stated, builds). Then
re-derive `weierstrassPreparation_exists` as
`weierstrassPreparation_exists_of_forall_exists (fun g' s' hg' f ↦ weierstrassDivision_exists hg' f hunit) hg`
and DELETE `weierstrassPreparation_exists_of_norm_eq_one` (the radius-1 residue engine, its
only consumer being the old proof) together with any now-unused local helpers. The residue
machinery in WeierstrassDivision.lean stays (division density needs it).
#### Proof sketch (the trick; verified in-session, recorded in decomposition.md tranche-2)
1. `hntR := hg.nontrivial`. Divide `X^s` by `g`: `hdiv g s hg (toRestricted c (X^s))` gives
   `q, r, rd, hXdiv`.
2. `ω := X^s − r`; coefficient block `hω_s`/`hω_gt` via `coeff_sub`, `coeff_X_pow`,
   `coeff_eq_zero_of_degree_lt rd`; `(hω_monic, hω_deg) := monic_and_degree_of_coeff`.
3. `hXn : ‖toRestricted c (X^s)‖ = c^s` (`monomial_one_right_eq_X_pow`,
   `toRestricted_monomial`, `norm_monomial`, `norm_one`); `rn : ‖toRestricted c r‖ ≤ c^s`
   from `norm_r_le_of_eq_mul_add c hg rd hXdiv` rewritten by `hXn`;
   `ωn := norm_toRestricted_X_pow_sub c rd rn`.
4. `hgq : g * q = toRestricted c ω := by rw [map_sub, hXdiv]; abel`.
5. `hω_dist := isDistinguished_toRestricted_of_monic hω_monic hω_deg ωn`.
6. Divide `g` by `toRestricted c ω`: `hdiv _ s hω_dist g` gives `P, S, hS, hgP`.
7. `hgqP : g = g * (q * P) + toRestricted c S := by rw [← mul_assoc, hgq]; exact hgP`.
8. `h1 : (1 : Restricted R c) = q * P := weierstrassDivision_q_unique c hg
   (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe s)
   (by rw [mul_one, map_zero, add_zero]) hS hgqP`.
9. `IsUnit P := isUnit_of_mul_eq_one P q (by rw [mul_comm]; exact h1.symm)`.
10. `g = P * toRestricted c ω` by `calc g = g * (q * P) = (g * q) * P = toRestricted c ω * P
    = P * toRestricted c ω` (`← h1, mul_one`; `ring`-steps; `hgq`; `mul_comm`).
#### Mathlib/project lemmas
`isUnit_of_mul_eq_one`, `WithBot.bot_lt_coe`; project `weierstrassDivision_q_unique`,
`norm_r_le_of_eq_mul_add`, `norm_toRestricted_X_pow_sub`,
`isDistinguished_toRestricted_of_monic`, `monic_and_degree_of_coeff` (all shipped).
#### Sources
Structural precedent: mathlib `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`
(adic preparation derived from division); derivation verified step-by-step in the tranche-2
planning session (decomposition.md).
#### Generality
`[NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]`, `Fact (0 < c)`
— NO `CompleteSpace`, NO `NeBot`: completeness enters only through the `hdiv` hypothesis.

### [CLEANUP-10] /cleanup on WeierstrassPrep.lean + WeierstrassDivision.lean (post-refactor)
- **Status**: done (2026-07-25; widths ≤100 both files, zero non-sorry warnings, no mechanical hits; trick body 43 lines (≤60); dead notations/opens removed with the engine; axioms standard on the moved trio + prep chain) | **Depends on**: T024, T025 | **Type**: cleanup (cadence + post-deletion sweep).

### [T026] Base change: `mapAlgebra` and its coe/norm/polynomial lemmas
- **Status**: done (2026-07-25; verbatim port compiled first build; val_mapAlgebra is rfl via codRestrict) | **File**: `BaseChange.lean` | **Depends on**: none | **Parallel**: yes | **Type**: def + lemma ×4
#### Statement
Skeleton `PowerSeries.isRestricted_mapAlgebra`, `Restricted.mapAlgebra`, `val_mapAlgebra`,
`norm_mapAlgebra`, `mapAlgebra_toRestricted` (canonical, builds).
#### Proof sketch (source: WPrep_gen.lean:910–949, verbatim modulo tree names)
1. `isRestricted_mapAlgebra` (:910–915): `isRestricted_iff` both sides; `hf.congr`;
   `coeff_map` + `hiso`.
2. `mapAlgebra` (:919–924): `RingHom.codRestrict ((PowerSeries.map (algebraMap K L)).comp
   (IsRestricted.subring c).subtype) (IsRestricted.subring c) fun f ↦
   isRestricted_mapAlgebra c hiso f.2`; `val_mapAlgebra := rfl` follows.
3. `norm_mapAlgebra` (:933–938): `norm_def` twice + `PowerSeries.gaussNorm_eq` twice +
   `iSup_congr` + `coeff_map` + `hiso`.
4. `mapAlgebra_toRestricted` (:941–949): `Subtype.ext` + `ext k` + `coeff_map`,
   `Polynomial.coeff_coe` ×2, `Polynomial.coeff_map`.
#### Mathlib lemmas
`PowerSeries.coeff_map`, `Polynomial.coeff_map`, `RingHom.codRestrict`, `iSup_congr`.
#### Sources
WPrep_gen.lean:910–949 (machine-checked at this pin).
#### Generality
`[NormedCommRing K] [NormedCommRing L] [Algebra K L]` + `IsUltrametricDist` for the subring;
`Fact (0 < c)` only on `norm_mapAlgebra`. No fields needed at this layer.

### [T027] `isDistinguished_mapAlgebra_iff`
- **Status**: done (2026-07-25; weighted-field port, compiled with one omit) | **File**: `BaseChange.lean` | **Depends on**: T026 | **Parallel**: no | **Type**: lemma
#### Statement
Skeleton `isDistinguished_mapAlgebra_iff` (canonical, builds).
#### Proof sketch (source: WPrep_gen.lean:954–980, fields now weighted)
1. `rw [val_mapAlgebra]`; termwise `hcoeff : ‖coeff k (map _ f.1)‖ = ‖coeff k f.1‖`
   (`coeff_map` + `hiso`) — the weighted Gauss terms are then literally equal.
2. `hgauss` via `gaussNorm_eq` ×2 + `iSup_congr`.
3. `hunit : IsUnit (coeff k (map _ f.1)) ↔ IsUnit (coeff k f.1)`: forward
   `isUnit_iff_ne_zero` (fields) + `(algebraMap K L).injective`-contrapositive
   (`map_zero`); backward `.map (algebraMap K L)`.
4. Both directions field-by-field as in the shipped `isDistinguished_rescaleEquiv_iff`.
#### Sources
WPrep_gen.lean:954–980.
#### Generality
Fields (`NontriviallyNormedField K/L`) — the unit-reflection direction genuinely uses
`isUnit_iff_ne_zero`; noted in the section docstring.

### [T028] `weierstrassDivision_descend` (+ private `lmap_mul`)
- **Status**: done (2026-07-25; 120-line port compiled after 3 fixes: imports Analysis.Normed.Module.FiniteDimension + LinearAlgebra.Basis.VectorSpace (leftInverse/continuity not in closure); NormedSpace must be letI (have-bound data instance triggered an unknown-free-variable elaboration bug); the known MonoidHomClass-synthesis quirk on the opaque Restricted hom struck again — map_mul won't fire via simp/rw on mapAlgebra, worked around with an explicit RingHom.map_mul summand in linear_combination. NOTE for CLEANUP/tranche-3: the recurring quirk (T021 IsUnit.map, here map_mul) suggests a missing/slow MonoidHomClass path on Restricted homs — worth a dedicated look) | **File**: `BaseChange.lean` | **Depends on**: T026, T027 | **Parallel**: no | **Type**: theorem
#### Statement
Skeleton `weierstrassDivision_descend` (canonical, builds); private
`lmap_mul (π : L →ₗ[K] K) (g : PowerSeries K) (h : PowerSeries L) : PowerSeries.mk (fun n ↦
π (coeff n (map (algebraMap K L) g * h))) = g * PowerSeries.mk fun n ↦ π (coeff n h)`.
#### Proof sketch (source: WPrep_gen.lean:985–1117, verbatim modulo tree names)
1. `lmap_mul` (:985–992): `ext` + `coeff_mk` + `coeff_mul` ×2 + `map_sum` +
   `← Algebra.smul_def, map_smul, smul_eq_mul` per summand.
2. `letI : NormedSpace K L` from `hiso` (`Algebra.smul_def` + `norm_mul`).
3. Retraction: `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)` (kernel
   `⊥` from `(algebraMap K L).injective`); bound via
   `SemilinearMapClass.bound_of_continuous π π.continuous_of_finiteDimensional`.
4. `hq0res`: coefficientwise retraction of `q` is restricted — `squeeze_zero` against
   `Cπ * (‖coeff n q.1‖ * c^n)` (`.const_mul` of `q.2`) (:1028–1037).
5. Retract the polynomial `r` coefficientwise (`∑ n ∈ r.support, monomial n (π (r.coeff n))`,
   coeff formula + degree bound, :1039–1051).
6. `hK`: apply `π` coefficientwise to the `L`-equation; `lmap_mul` pulls the product back;
   term-mode `show`s across the seam exactly as source (:1053–1086).
7. `hzero`: the `L`-side difference is a division of `0` (`linear_combination hf − hmapK`,
   :1088–1096); kill it with `norm_q_le_of_eq_mul_add`/`norm_r_le_of_eq_mul_add` at `L`
   (general-`c`, hypothesis-free — the point of the whole design) + `norm_le_zero_iff`
   (:1097–1114); assemble (:1115–1117).
#### Mathlib lemmas
`LinearMap.exists_leftInverse_of_injective`, `SemilinearMapClass.bound_of_continuous`,
`LinearMap.continuous_of_finiteDimensional`, `squeeze_zero`, `Algebra.smul_def`,
`Algebra.linearMap` (all used by the compiled legacy at this pin).
#### Sources
WPrep_gen.lean:985–1117 (machine-checked; 130 source lines → expect ~120 Lean).
#### Generality
`[CompleteSpace K] [Module.Finite K L]` over `NontriviallyNormedField`s; no completeness
of `L` (the source omits it).

### [CLEANUP-11] /cleanup on BaseChange.lean (final)
- **Status**: done (2026-07-25; widths ok, no mechanical hits (one legitimate letI, documented), warning-free, axioms standard ×6) | **Depends on**: T026, T027, T028 | **Type**: cleanup (cadence: 3 tickets + final).

### [T029] `MemDivisibleValueGroup` API + `exists_norm_inv_isUnit`
- **Status**: done (2026-07-25; compiled first build; achieving index via shipped exists_achievesGaussNorm + norm_def) | **File**: `DivisibleRadius.lean` | **Depends on**: none | **Parallel**: yes | **Type**: def-API + lemma
#### Statement
Skeleton `memDivisibleValueGroup_of_norm_eq`, `exists_norm_inv_isUnit` (canonical, builds).
#### Proof sketch
1. `memDivisibleValueGroup_of_norm_eq`: `⟨1, one_ne_zero, x, by rw [hx, pow_one]⟩`.
2. `exists_norm_inv_isUnit` (source WPrep_gen.lean:884–899): achieving index via the shipped
   `exists_achievesGaussNorm c f`; `hnorm : ‖f‖ = ‖coeff k f.1‖ * c^k` via `norm_def`;
   coefficient nonzero (else `‖f‖ = 0` contra `norm_pos_iff.mpr hf`); take
   `a := (coeff k f.1 * (u : K)^k)⁻¹`; `norm_inv`, `norm_mul`, `norm_pow`, `hu`, `← hnorm`;
   `isUnit_iff_ne_zero` + `inv_ne_zero` + `mul_ne_zero` + `pow_ne_zero`.
#### Mathlib lemmas
`norm_inv` (NormedDivisionRing), `isUnit_iff_ne_zero`, `inv_ne_zero`, `pow_ne_zero`.
#### Sources
WPrep_gen.lean:884–899 (machine-checked); resolves the `hunit`-discharge question raised in
the docstring review as public API.
#### Generality
Field-level (`NontriviallyNormedField K`); this is the lemma that is genuinely field-only.

### [T030] `weierstrassDivision_exists_divisible`
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: T028, T029, CLEANUP-11 | **Parallel**: no | **Type**: theorem
- **Progress**: ported :1195–1244 verbatim modulo tree names. Imports added: `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`. Notation notes: `K⟮α⟯` needs `open IntermediateField in` and `𝓝[≠]` needs `open scoped Topology in`, both placed BEFORE the docstring (same parse rule as `omit ... in`). `NontriviallyNormedField E` and `NormedSpace K E` are `letI` (data, participate in elaboration); the rest `haveI`. `hfin` needed `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral` + `Algebra.IsAlgebraic.of_finite` for the descent's Algebra.IsAlgebraic. Compiles green.
#### Statement
Skeleton `weierstrassDivision_exists_divisible` (canonical, builds).
#### Proof sketch (source: WPrep_gen.lean:1195–1244, verbatim modulo tree names)
1. Destructure `hdiv` as `⟨n, hn, x, hx⟩`; root `α` of `algebraMap K (AlgebraicClosure K) x`
   via `IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_ne_zero hn)`.
2. Instance block on `E := K⟮α⟯` (:1205–1215): `adjoin.finiteDimensional` (integral since
   algebraic), `spectralNorm.nontriviallyNormedField K E`,
   `IsUltrametricDist` from `isNonarchimedean_spectralNorm`, `NormedSpace` from
   `spectralNorm_extends`, `CompleteSpace` from `FiniteDimensional.complete`,
   `NeBot` from `NormedField.nhdsNE_neBot`.
3. `‖gen‖ = c` via `pow_left_inj₀` + `norm_pow` + `hgen` + `spectralNorm_extends` + `hx`
   (:1217–1227); `hunitE : ∃ u : Eˣ, ‖u‖ = c` (`Units.mk0`).
4. Divide over `E` with the shipped hunit-version `weierstrassDivision_exists`
   (`hg` transported by `isDistinguished_mapAlgebra_iff`, `hunit` discharged by
   `exists_norm_inv_isUnit hunitE`); descend by `weierstrassDivision_descend` (:1236–1244).
#### Mathlib lemmas
`IsAlgClosed.exists_pow_nat_eq`, `IntermediateField.adjoin.finiteDimensional`,
`spectralNorm.nontriviallyNormedField`, `spectralNorm_extends`,
`isNonarchimedean_spectralNorm`, `FiniteDimensional.complete`, `NormedField.nhdsNE_neBot`,
`pow_left_inj₀`, `IntermediateField.AdjoinSimple.algebraMap_gen`, `Units.mk0` (all used by
the compiled legacy at this pin).
#### Sources
WPrep_gen.lean:1195–1244 (machine-checked; 50 source lines → ~60 Lean).
#### Generality
`NontriviallyNormedField K`, complete, ultrametric; NO `hunit`/`h` in the statement.

### [T031] `weierstrassDivision_uniqueness_divisible` + `weierstrassDivision_polynomial_divisible`
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: T030 | **Parallel**: no | **Type**: theorem ×2
- **Progress**: both mirror the shipped hunit-version bodies verbatim with `weierstrassDivision_exists_divisible hdiv` / `_uniqueness_divisible hdiv` replacing the hunit calls; `Polynomial.toRestricted_injective` + `weierstrassDivision_q_unique c hg` unchanged. Compiles green first try.
- **SUPERSEDED (2026-07-25 post-completion audit)**: both theorems deleted — strictly weaker than the `_of_field` counterparts (extra `MemDivisibleValueGroup` hypothesis, same conclusion) and consumed only by the equally-dead T032 trio. `weierstrassDivision_exists_divisible` survives as `private` (it is the divisible branch of `exists_of_field`).
#### Proof sketch
1. Uniqueness (source :1246–1256): exists (T030) + `Polynomial.toRestricted_injective` on the
   remainder-cancellation + shipped `weierstrassDivision_q_unique` — mirror the shipped
   hunit-version verbatim.
2. Polynomial (source :1258–1314): monic-rescale `C ↑u⁻¹ * g₀`
   (`monic_C_mul_of_mul_leadingCoeff_eq_one`), `modByMonic_add_div`/`degree_modByMonic_lt`,
   bridge through uniqueness_divisible via the `key` argument — mirror the shipped
   `weierstrassDivision_polynomial` verbatim with `_divisible` inputs (no witnesses needed).
#### Sources
WPrep_gen.lean:1246–1314; project shipped `weierstrassDivision_uniqueness`/`_polynomial`
(same K-level shapes).

### [CLEANUP-12] /cleanup on DivisibleRadius.lean (partial)
- **Status**: done (2026-07-25) | **Depends on**: T029, T030, T031 | **Type**: cleanup (cadence: 3rd ticket on file).
- **Progress**: `lake build` green (2570 jobs); `#print axioms` standard on all 4 namespace decls (root-level `memDivisibleValueGroup_of_norm_eq` is a 1-line constructor); golfed `IntermediateField.`-prefixes under the existing `open ... in` and anonymized unused `hfin` binder; no lint warnings besides expected sorries.

### [T032] Preparation at divisible radii (corollary trio)
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: CLEANUP-12, T025 | **Parallel**: no | **Type**: theorem ×3
- **Progress**: exists = one-line trick instantiation; unique/polynomial mirror the shipped bodies with `_divisible` calls. The shipped polynomial body's `exists_units_norm_eq`+`hwitness` block is dead code — dropped entirely (no witnesses needed). Skeleton's spurious `hgs : g₀.degree ≤ s` on `_polynomial_divisible` removed (shipped analogue has none; division runs against monic ω via `ωd.le`); NOTE the `_of_field` polynomial-prep skeleton (T038) carries the same spurious `hgs` — drop it there too. All green.
- **SUPERSEDED (2026-07-25 post-completion audit)**: all three deleted. The `_of_field` prep trio is built directly on `weierstrassDivision_*_of_field` via the trick and never consumed the `_divisible` prep rung — the trick makes prep a corollary of division at every generality, so intermediate-rung prep statements are never needed. Also deleted the consumer-less `memDivisibleValueGroup_of_norm_eq`. User approved the prune (sanity-check audit).
#### Proof sketch
1. `weierstrassPreparation_exists_divisible := weierstrassPreparation_exists_of_forall_exists
   (fun g' s' hg' f ↦ weierstrassDivision_exists_divisible hdiv hg' f) hg` — one line.
2. `_unique_divisible`: mirror the shipped `weierstrassPreparation_unique` body verbatim
   (norm-cancellation against `c^s ≠ 0`; `degree_sub_lt` on equal-degree monics;
   `norm_r_le_of_eq_mul_add` at `f := 0`; `toRestricted_injective`) with `_divisible` exists.
3. `_polynomial_divisible`: mirror the shipped `weierstrassPreparation_polynomial` body with
   `weierstrassDivision_polynomial_divisible` + `weierstrassDivision_q_unique` (no witness
   adjustments needed — the `_divisible` division takes none).
#### Sources
Project shipped WeierstrassPrep.lean (the three K-level bodies); WPrep_gen.lean §5
:1316–1626 confirms the K-level character ("uniqueness and the polynomial refinements are
then K-level arguments on top of the unit-free bounds").

### [T033] Contraction-factor extraction for strictly-dominated series
- **Status**: done (2026-07-25) | **File**: `WeierstrassDivision.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma
- **Progress**: proved per sketch (window `(range N).erase s`, `θ := max (F.max' hF) (M/2) / M`, tail via `Metric.tendsto_atTop` at `M/2`). `F.max' < M` shown via `F.max'_mem` + image-destructure (avoids `Finset.max'_lt_iff` arity risk); `omit [NormMulClass R]` added. Green first try.
#### Statement
Skeleton `exists_lt_one_forall_norm_coeff_mul_pow_le` (canonical, builds).
#### Proof sketch (source: project shipped `exists_lt_one_forall_norm_coeff_le`, same skeleton windowed over all `t ≠ s`)
1. `M := ‖coeff s g.1‖ * c^s = ‖g‖` (`norm_coeff_mul_pow_eq`), `0 < M` (`hg.norm_pos`).
2. Tail: `(isRestricted_iff' c g.1).mp g.2` + `Metric.tendsto_atTop` at `M/2` gives `N` with
   all Gauss terms `< M/2` from `N` on.
3. Window: `F := ((Finset.range N).erase s).image (fun t ↦ ‖coeff t g.1‖ * c^t)`; every
   element `< M` by `hstrict`; case `F.Nonempty`: `θ := max (F.max' hF) (M/2) / M`
   (`0 ≤`, `< 1` by `div_lt_one` + `max_lt`); bound: `t < N, t ≠ s` → in `F` → `≤ F.max'`;
   `N ≤ t` → `≤ M/2`; both `≤ θ * M` by `le_div_iff₀`-algebra. Case empty: `θ := 1/2`,
   tail-only.
#### Mathlib lemmas
`Metric.tendsto_atTop`, `Finset.max'`/`le_max'`, `div_lt_one`, `le_div_iff₀`.
#### Sources
Project shipped `exists_lt_one_forall_norm_coeff_le` (WeierstrassDivision.lean, T012) —
identical architecture with the window `erase s` and normalisation by `M`.
#### Generality
General `R` (Bounds-section context), general `c`.

### [T034] The one-step approximate division (strictly-dominated case)
- **Status**: done (2026-07-25) | **File**: `WeierstrassDivision.lean` | **Depends on**: T024, T033 | **Parallel**: no | **Type**: lemma
- **Progress**: proved per BGR sketch (~75 LOC). Deviations from sketch: (a) `norm_units_inv` needs `NormOneClass R` absent from Bounds section — derived `hui : ‖↑u⁻¹‖ = ‖↑u‖⁻¹` locally from `Nontrivial R` (`‖1‖=1` via `mul_right_cancel₀`, then `inv_eq_of_mul_eq_one_right`); (b) key-identity coefficient via `monomial_eq_C_mul_X_pow` + `coeff_C_mul` + `coeff_X_pow_mul'` (no single-var `coeff_monomial_mul` in mathlib) with `rcases lt_or_ge` instead of `split_ifs` (`le_or_lt` gone at this pin); (c) `norm_le_iff` takes `c` explicitly; (d) final cancel via `mul_inv_cancel_left₀` (bare `← mul_assoc` rewrites the wrong occurrence). Green.
#### Statement
```lean
lemma exists_mem_divisionSet_norm_le_of_forall_le {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hbd : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t ≤ θ * (‖coeff s g.1‖ * c ^ s))
    (f : Restricted R c) : ∃ b ∈ divisionSet g s, ‖-f + b‖ ≤ θ * ‖f‖ := by
  sorry
```
(Skeleton lands with T024's general-`c` `divisionSet`.)
#### Proof sketch (BGR §5.2.1/2 successive-approximation induction step; prose verified in decomposition.md tranche-2)
1. `hntR := hg.nontrivial`; `u := hg.isUnit_coeff.unit`; `M := ‖coeff s g.1‖ * c^s = ‖g‖ > 0`.
2. Quotient step `qf : Restricted R c := ⟨PowerSeries.mk fun n ↦ ↑u⁻¹ * coeff (n + s) f.1, _⟩`;
   restrictedness: Gauss terms are `(‖↑u⁻¹‖ * c^(−s))`-multiples of the shifted terms of `f`
   (`norm_mul`, `norm_units_inv`); null by `isRestricted_iff'` + shift
   (`Filter.tendsto_add_atTop_iff_nat`) + `const_mul`.
3. Remainder `rf := PowerSeries.trunc s f.1` (`degree_trunc_lt`);
   `b := g * qf + toRestricted c rf ∈ divisionSet g s` by construction.
4. Key identity `monomial c s (coeff s g.1) * qf = f − toRestricted c rf`: `Subtype.ext` +
   `ext m`; coeff of monomial-mul (`monomial = C·X^s`: `coeff_C_mul` + `coeff_X_pow_mul`,
   or `PowerSeries.coeff_monomial_mul` if present) gives `b_s·(u⁻¹·f_m) = f_m` for `s ≤ m`
   (`Units.mul_inv_cancel_left`) and `0` below; RHS via `coeff_trunc`.
5. `-f + b = (g − monomial c s (coeff s g.1)) * qf` (`sub_mul` + step 4 + `abel`-algebra).
6. `‖g − monomial c s (coeff s g.1)‖ ≤ θ * M` by `norm_le_iff`: coefficientwise
   `val_sub`/`val_monomial` + `PowerSeries.coeff_monomial`; at `t = s` the coefficient is
   `0`; at `t ≠ s` it is `coeff t g.1` and `hbd` applies.
7. `‖qf‖ ≤ M⁻¹ * ‖f‖` by `norm_le_iff`: term `n` is
   `(‖coeff s g.1‖ * c^s)⁻¹ · (‖coeff (n+s) f.1‖ * c^(n+s))` after `norm_units_inv` and
   `pow_add` bookkeeping, `≤ M⁻¹‖f‖` by `norm_coeff_mul_pow_le`.
8. Conclude: `‖-f + b‖ = ‖g − monomial‖·‖qf‖ ≤ (θM)(M⁻¹‖f‖) = θ‖f‖` (`norm_mul`,
   `mul_le_mul`, cancel `M ≠ 0`).
#### Mathlib lemmas
`PowerSeries.trunc`, `PowerSeries.coeff_trunc`, `PowerSeries.degree_trunc_lt`,
`Filter.tendsto_add_atTop_iff_nat`, `Units.mul_inv_cancel_left`,
`PowerSeries.coeff_monomial`; project `norm_le_iff`, `norm_coeff_mul_pow_le`,
`norm_units_inv`, `val_monomial`.
#### Sources
BGR (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*) §5.2.1 Prop 2 / §5.2.2 Thm 1 —
the induction step of the classical successive-approximation division; full prose in
decomposition.md tranche-2 (no legacy Lean exists — new mathematics, ~60 LOC expected
against the one-paragraph BGR step).
#### Generality
General `R` (no field, no `hunit`), general `c`; the contraction hypothesis `hbd` is the
interface to T033.

### [T035] Density and existence for strictly-dominated divisors
- **Status**: done (2026-07-25) | **File**: `WeierstrassDivision.lean` | **Depends on**: T034 | **Parallel**: no | **Type**: lemma + theorem
- **Progress**: both mirror the shipped radius-1 bodies. One deviation: `AddSubgroup.dense_of_infDist_le` needs `0 < ε` but T033 only gives `0 ≤ θ` — passed `ε := max θ (1/2)` (still `< 1`, and `θ * ‖f‖ ≤ max θ (1/2) * ‖f‖`). WeierstrassDivision.lean is now SORRY-FREE. Green.
#### Statement
```lean
lemma dense_divisionSet_of_forall_lt {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s) :
    Dense (divisionSet g s) := by
  sorry

theorem weierstrassDivision_exists_of_forall_lt {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s)
    (f : Restricted R c) :
    ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  sorry
```
#### Proof sketch
1. Dense: obtain `θ` from T033; mirror the shipped `dense_divisionSet` verbatim
   (`AddSubgroup.dense_of_infDist_le` with `ε := θ`; `f = 0` via `infDist_zero_of_mem` +
   `positivity`; `f ≠ 0` via T034 + `infDist_le_dist_of_mem` + `dist_eq_norm` juggle) —
   θ < 1 comes from T033, θ ≥ 0 likewise.
2. Existence: mirror the shipped `weierstrassDivision_exists_of_norm_eq_one` capstone
   (closure of closed = itself + dense closure = univ) with T024's general-`c`
   `isClosed_divisionSet`.
#### Sources
Project shipped `dense_divisionSet` + `weierstrassDivision_exists_of_norm_eq_one`
(identical architecture at radius 1); AddSubgroup.dense_of_infDist_le (BGR 1.1.4/2).
#### Generality
General `R`, general `c`, NO scaling hypotheses — the strictly-dominated engine.

### [CLEANUP-14] /cleanup on WeierstrassDivision.lean (final, tranche 2)
- **Status**: done (2026-07-25) | **Depends on**: T033, T034, T035, CLEANUP-10 | **Type**: cleanup (cadence: 3 tickets + final).
- **Progress**: module builds green (2207 jobs, zero warnings — file sorry-free); `#print axioms` standard on all 4 new decls; line-width audit clean (awk byte-counts were false positives — python char-count shows ≤ 100 everywhere); dropped unused `set ... with` names in T034; rebuilt green.

### [T036] No ties off the divisible closure
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: T029 | **Parallel**: yes | **Type**: lemma
- **Progress**: proved per sketch; t>s branch is `hg.lt_of_gt` verbatim; t<s ties give `c^(s-t) = ‖coeff t g.1 * ↑u⁻¹‖` via `pow_sub₀` + locally-derived `‖↑u⁻¹‖ = ‖↑u‖⁻¹` (NormOneClass-free, same derivation as T034) + `field_simp`/`linear_combination heq`. Green first try.
#### Statement
Skeleton `forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup` (canonical, builds).
#### Proof sketch (in-session prose, decomposition.md tranche-2)
1. `hntR := hg.nontrivial`; fix `t ≠ s`. `≤` from `norm_coeff_mul_pow_le` +
   `hg.norm_coeff_mul_pow_eq`; upgrade to `<` by excluding equality.
2. Suppose `‖coeff t g.1‖ * c^t = ‖coeff s g.1‖ * c^s`. For `t > s` this contradicts
   `hg.lt_of_gt` directly. For `t < s`: `u := hg.isUnit_coeff.unit`;
   `‖coeff s g.1‖ > 0` (unit + `Nontrivial`), so dividing and using
   `pow_sub₀ (Fact.out : 0 < c).ne'` gives `c ^ (s − t) = ‖coeff t g.1‖ * ‖coeff s g.1‖⁻¹
   = ‖coeff t g.1 * ↑u⁻¹‖` (`norm_mul` + `norm_units_inv`) — exhibiting
   `MemDivisibleValueGroup R c` with `n := s − t ≠ 0` (`Nat.sub_ne_zero_of_lt`),
   contradicting `hc`.
#### Mathlib lemmas
`pow_sub₀`, `Nat.sub_ne_zero_of_lt`; project `norm_units_inv`, `norm_coeff_mul_pow_le`,
`norm_coeff_mul_pow_eq`, `IsDistinguished.nontrivial`.
#### Sources
In-session derivation (two-line units computation), recorded with the dichotomy design in
decomposition.md tranche-2; this is the pivot of the dichotomy replacing density+limits.
#### Generality
General `R` with `NormMulClass` (the `NoTie` section) — deliberately not field-only.

### [CLEANUP-ALL-3] /cleanup-all before the every-radius milestones
- **Status**: done (2026-07-25) | **Depends on**: CLEANUP-10, CLEANUP-11, CLEANUP-12, CLEANUP-14, T032, T036 | **Type**: cleanup-all.
- **Progress**: full `lake build` green; sorry inventory across the Restricted tree at that point = exactly the 6 `_of_field` skeletons (NewtonPolygon.lean's sorries are a separate pre-existing development, not on this board); per-file cleanups already done in CLEANUP-12/14.

### [T037] MILESTONE: Weierstrass division at every radius (field)
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: CLEANUP-ALL-3 | **Parallel**: no | **Type**: theorem ×3
- **Progress**: exists = 4-line by_cases exactly per sketch; uniqueness/polynomial mirror the `_divisible` bodies with `_of_field` calls. All green first try; axioms standard.
#### Statement
Skeleton `weierstrassDivision_exists_of_field`, `_uniqueness_of_field`,
`_polynomial_of_field` (canonical, builds; `_of_field` naming flagged for final cleanup).
#### Proof sketch
1. Exists: `by_cases hdiv : MemDivisibleValueGroup K c`; yes →
   `weierstrassDivision_exists_divisible hdiv hg f`; no →
   `weierstrassDivision_exists_of_forall_lt hg
   (forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup hdiv hg) f`.
2. Uniqueness: exists + `toRestricted_injective` + shipped `weierstrassDivision_q_unique`
   (mirror the shipped shape).
3. Polynomial: mirror the shipped `weierstrassDivision_polynomial` body with the
   `_of_field` uniqueness.
#### Sources
Assembly of T030/T031/T035/T036; K-level bridging identical to shipped bodies.

### [T038] MILESTONE: Weierstrass preparation at every radius (field)
- **Status**: done (2026-07-25) | **File**: `DivisibleRadius.lean` | **Depends on**: T037, T025 | **Parallel**: no | **Type**: theorem ×3
- **Progress**: exists = one-line trick instantiation; unique/polynomial mirror the `_divisible` prep bodies. Spurious `hgs` dropped from `_polynomial_of_field` (as flagged in T032). DivisibleRadius.lean is SORRY-FREE; all 6 milestone theorems + 4 earlier decls axiom-checked standard.
#### Proof sketch
1. Exists: `weierstrassPreparation_exists_of_forall_exists
   (fun g' s' hg' f ↦ weierstrassDivision_exists_of_field hg' f) hg` — one line.
2. Unique / polynomial: mirror the shipped prep bodies with `_of_field` inputs.
#### Sources
T025 trick + T037; shipped WeierstrassPrep.lean K-level bodies.

### [CLEANUP-13] /cleanup on DivisibleRadius.lean (final)
- **Status**: done (2026-07-25) | **Depends on**: T037, T038 | **Type**: cleanup (final per-file; includes the `_of_field` naming decision with the user).
- **Progress**: module green, zero warnings; all 10 decls axiom-standard; duplicated hand-rolled `‖1‖ = 1`/`‖↑u⁻¹‖ = ‖↑u‖⁻¹` derivations in T034/T036 replaced by mathlib's `NormMulClass.toNormOneClass` + `norm_units_inv`; char-width audit clean. **OPEN USER DECISION**: `_of_field` naming — whether the six unconditional theorems should take over the bare `weierstrassDivision_*`/`weierstrassPreparation_*` names (demoting the `hunit` versions to `_of_exists_norm_inv` or similar) or keep the `_of_field` suffix. Provisional names left in place; module doc carries the naming note.

### [CLEANUP-FINAL-2] /cleanup-all on the whole development (tranche 2)
- **Status**: done (2026-07-25) | **Depends on**: everything above | **Type**: cleanup-all (final).
- **Progress**: all 14 Restricted modules built individually green (Basic → DivisibleRadius, 2570 jobs at the deepest); `grep sorry PhD/ForMathlib/RingTheory` = 0; no `axiom` declarations anywhere in the tree; boards/tickets all closed. TRANCHE 2 COMPLETE — Weierstrass division + preparation (exists/unique/polynomial) hold at every radius `c > 0` over a complete nontrivially normed ultrametric field with NO scaling hypotheses.

---

# Tranche 4 board (2026-07-25): every-polyradius Mv Weierstrass via Gauss extensions

Decomposition: `.mathlib-quality/decomposition.md` — tranche-3 sections D/W/B/E (legacy-backed,
quotes at WPPrep_MV.lean line numbers) + tranche-3b sections G-A…G-I (Gauss layer, prose +
attacks). All statements are canonical in the skeletons (build green, 2642 jobs). Binding
obligations from the artifact: G-D instance-diamond assembly note (field instance must SHARE
ring/norm data); G-B ℤ-sign split; div-polynomial keeps `hgs`, prep-polynomial has none.
Summary: 21 proof tickets (T039–T059) + 11 cleanups. Parallel at peak: T039 ∥ T048 ∥ T050 ∥ T052.

### [T039] Gauss-norm basics I (LaurentPolynomial)
- **Status**: done (2026-07-25) — 5 lemmas + private `bddAbove_range_gaussTerm` proven; support via `p.coeff.support` (coeff is a Finsupp); `AddMonoidAlgebra.coeff_zero` for the zero case; omits added (Fact-free where positivity unused). | **File**: `LaurentPolynomial/GaussNorm.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma ×5
- **Statement**: skeletons `gaussNorm_nonneg`, `le_gaussNorm`, `exists_gaussNorm_eq`, `gaussNorm_zero`, `gaussNorm_eq_zero_iff` (canonical, build).
- **Sketch**: decomposition G-A: iSup over ℤ of `‖p.coeff m‖ * r ^ m` (zpow!), zero off finite support ⇒ BddAbove (range ⊆ insert 0 (finite image)); `le_ciSup`; attained via the support finset max; eq-zero-iff from attainment + `zpow_pos`. Mirror the Mv `GaussNorm.lean` proofs at finite support. Mathlib: `le_ciSup`, `ciSup_le`, `Real.iSup_nonneg`, `zpow_pos`. API risk flagged: support access on the `AddMonoidAlgebra` structure — fall back to `Function.support` finiteness if needed.
- **Generality**: `[NormedCommRing R]`, `[Fact (0 < r)]`; ultrametricity not needed here.

### [T040] Gauss-norm values and bounds
- **Status**: done (2026-07-25) — DEVIATION: `gaussNorm_T` gained `[NormOneClass R]` (‖1‖=1 is not free over a general normed ring — adversarial catch; all consumers are fields). `T_apply`-rewrites need `simp only [T_apply]` first (polymorphic-ite Semiring-meta stuck under bare rw); `le_gaussNorm r (T m : R[T;T⁻¹]) m` needs the ascription. mul_le via single product-sum (`coeff_mul` + `Finset.sum_product` + `rfl`) + `IsNonarchimedean.finset_image_add`. | **File**: `LaurentPolynomial/GaussNorm.lean` | **Depends on**: T039 | **Parallel**: no | **Type**: lemma ×4
- **Statement**: skeletons `gaussNorm_C`, `gaussNorm_T`, `gaussNorm_add_le`, `gaussNorm_mul_le`.
- **Sketch**: G-A: singleton-support collapse for `C`/`T` (`C_apply`/`T_apply` mathlib, read at pin); add ≤ max and mul ≤ coefficientwise (finite antidiagonal + `IsUltrametricDist.norm_add_le_max`-family, as in the Mv file).

### [T041] No ties and multiplicativity off the divisible closure
- **Status**: done (2026-07-25) — sign split executed both ways (witnesses `(j-i).toNat`/`(i-j).toNat`, `field_simp` + `linear_combination ±h`); private `norm_add_eq_left_of_norm_lt` isoceles helper added (no mathlib norm_add_eq lemma found in Ultra.lean — G2: greps on Group/Ultra + Ring/Ultra); dominant-term argument via `Finset.add_sum_erase` + strictness from tie-injectivity; `lt_of_mul_lt_mul_right` instead of iff-rw (`mul_lt_mul_right` iff-form demanded a missing `MulLeftStrictMono` synthesis). | **File**: `LaurentPolynomial/GaussNorm.lean` | **Depends on**: T040 | **Parallel**: no | **Type**: lemma ×2
- **Statement**: skeletons `gaussTerm_injOn_of_not_memDivisibleValueGroup`, `gaussNorm_mul`.
- **Sketch**: G-B (BINDING sign split): tie with `i > j` ⇒ `r^(i-j) = ‖b * a⁻¹‖`, witness `(i-j).toNat`; `i < j` symmetric with `a * b⁻¹`. Multiplicativity: unique dominant exponents, dominant product term strictly dominates the antidiagonal (ultrametric), squeeze with T040's `mul_le`. Needs `[NormedField K]`.

### [CLEANUP-15] /cleanup on GaussNorm.lean (cadence)
- **Status**: done (2026-07-26) — build green, axioms standard (gaussNorm_mul etc.), width clean. | **Depends on**: T039, T040, T041 | **Type**: cleanup.

### [T042] GaussLaurent instance pack
- **Status**: done (2026-07-26) — gaussRingNorm fields all discharged from T039–T041; standalone Norm instance DELETED (would diamond with RingNorm.toNormedRing's — canonical-uniformity pattern per Mv GaussNorm.lean:173) and `norm_def := rfl` added; `gaussNorm_neg`/`coeff_add_apply`/`coeff_sub_apply` Laurent-level helpers added (synonym-seam: coeff-rewrites only fire at Laurent spelling; GaussLaurent-side uses exact-defeq bridges); NormOneClass [NormOneClass K] instance added (needed by T047); NormMulClass one-liner from T041. | **File**: `LaurentPolynomial/GaussNorm.lean` | **Depends on**: CLEANUP-15 | **Parallel**: no | **Type**: instances
- **Statement**: skeleton `gaussRingNorm` (5 prop fields), `IsUltrametricDist`, `norm_C`, `norm_T`, `NormMulClass` [Fact ¬MemDVG].
- **Sketch**: G-C: fields = T039–T041 results through the synonym; instance path `RingNorm.toNormedRing` is fixed (canonical uniformity for Completion — same pattern as Mv GaussNorm.lean:173).

### [T043] coeffZero
- **Status**: done (2026-07-26) — coeffZero via exact-defeq bridges; map_smul' through `coeff_single_zero_mul` + a trailing rfl (smul defeq C·mul via toAlgebra). | **File**: `LaurentPolynomial/GaussNorm.lean` | **Depends on**: T042 | **Parallel**: no | **Type**: def-completion ×4
- **Statement**: skeleton `coeffZero` (map_add', map_smul'), `coeffZero_C`, `norm_coeffZero_le`.
- **Sketch**: G-C: coefficientwise; smul via the `C.toAlgebra` instance (coeff of `C a * p` at 0 — Laurent mul-by-C lemma); bound: one term of the sup, `r ^ (0:ℤ) = 1`.

### [CLEANUP-16] /cleanup on GaussNorm.lean (final)
- **Status**: done (2026-07-26) — GaussNorm.lean sorry-free, 2572 jobs green, axioms standard on gaussRingNorm/coeffZero/norm_T. | **Depends on**: T042, T043 | **Type**: cleanup (final per-file).

### [T044] Completion normed-ring pack
- **Status**: done (2026-07-26) — MATHLIB-GAP FILLED: NormedCommRing on the completion assembled from separately-declared transported NormedAddCommGroup + CommRing instances (structure-source elaborator can't see through the synonym in one step — `inferInstanceAs` per instance first, then `{i1, i2 with}`); norm_mul_le/ultrametric by `Completion.induction_on₂` + `isClosed_le` with coe-case `show` at Completion spelling (coe_mul/coe_add rewrites only fire there). PR-able upstream. | **File**: `LaurentPolynomial/GaussExtension.lean` | **Depends on**: CLEANUP-16 | **Parallel**: no | **Type**: instances + lemma ×3
- **Statement**: skeletons `NormedCommRing (GaussExtension K r)` instance, `IsUltrametricDist`, `CompleteSpace`, `ofLaurent`, `norm_ofLaurent`, `denseRange_ofLaurent`.
- **Sketch**: G-D: ring from `Topology/Algebra/UniformRing`; norm layer from `Analysis/Normed/Group/Completion` (`Completion.norm_coe`); `norm_mul_le` extends by density (MATHLIB GAP leaf — build the general `NormedRing (Completion A)` assembly, PR-able); `ofLaurent := Completion.coeRingHom`; density = `Completion.denseRange_coe`.

### [T045] Algebra structure and value-group lemmas
- **Status**: done (2026-07-26) — algebra isometry, unit T (norm r via [NormOneClass K] — deviation, same justification as T040), memDVG self + of_base. | **File**: `LaurentPolynomial/GaussExtension.lean` | **Depends on**: T044 | **Parallel**: no | **Type**: lemma ×4
- **Statement**: skeletons `norm_algebraMap`, `exists_unit_norm`, `memDivisibleValueGroup_self`, `memDivisibleValueGroup_of_base`.
- **Sketch**: G-D: isometry through `norm_ofLaurent` + T042 `norm_C`; unit = image of the Laurent unit `T` (`isUnit_T`, `RingHom.isUnit_map` — remember the MonoidHomClass quirk), norm r via `norm_T`; memDVG witnesses transported.

### [T046] The Gauss retraction
- **Status**: done (2026-07-26) — retraction built from Completion.extension of coeffZero; additivity/C-mul laws proven as standalone Completion-spelling helpers (instances verified firing there by probe) with thin defeq wrappers for the LinearMap fields; norm-1 bound by induction_on + term-mode norm_coe (rw-pattern flaky in one goal). | **File**: `LaurentPolynomial/GaussExtension.lean` | **Depends on**: T044 | **Parallel**: with T045 | **Type**: def-completion ×3
- **Statement**: skeletons `retraction`, `retraction_algebraMap`, `norm_retraction_le`.
- **Sketch**: G-E: `Completion.extension` of T043's `coeffZero` (uniformly continuous via the norm-1 bound, `LipschitzWith.uniformContinuous`); linearity + bound by `Completion.induction_on` density; `extension_coe` on constants.

### [CLEANUP-17] /cleanup on GaussExtension.lean (cadence)
- **Status**: done (2026-07-26) — chain green through retraction. | **Depends on**: T044, T045, T046 | **Type**: cleanup.

### [T047] The Gauss-point field instance
- **Status**: done (2026-07-26) — THE GAUSS-POINT FIELD: isUnit_of_ne_zero per the G-F prose (density approximant of equal norm via isoceles; unique dominant monomial `single m a = C a * T m` unit; tail strictly smaller by tie-injectivity; `Units.oneSub` geometric series; algebra slip in the U−x split caught by `ring` and fixed: −(p−q)+(p−x)); Field via IsField.toField; NontriviallyNormedField assembled SHARING NormedCommRing+Field data (binding G-D note satisfied — no diamond); NormMulClass by density. GaussExtension.lean SORRY-FREE. | **File**: `LaurentPolynomial/GaussExtension.lean` | **Depends on**: CLEANUP-17, T041 | **Parallel**: no | **Type**: instances
- **Statement**: skeletons `NontriviallyNormedField (GaussExtension K r)` [Facts], `NormMulClass`.
- **Sketch**: G-F + BINDING G-D assembly note: `IsField` by density (approximate x by Laurent p with `‖x - p‖ < ‖x‖`, isoceles ⇒ `‖p‖ = ‖x‖`; unique dominant monomial (T041) is a unit; `1 + small` inverts by geometric series in the complete ring, cf. `Units.oneSub`); then `IsField.toField` SHARING the CommRing, and NontriviallyNormedField assembled with `__ := inferInstanceAs (NormedCommRing _)` — the skeleton's temporary instance diamond MUST be eliminated here. Nontriviality witness from `K`. NormMulClass by density from T041.

### [CLEANUP-18] /cleanup on GaussExtension.lean (final)
- **Status**: done (2026-07-26) — GaussExtension.lean sorry-free (2575 jobs); NontriviallyNormedField probe resolves; axioms standard; width clean. | **Depends on**: T047 | **Type**: cleanup (final per-file).

### [T048] Mv transport dictionary I
- **Status**: done (2026-07-26) — D1–D4: unfold+apply_symm_apply; Iso lemmas take c explicitly (norm_finSuccEquiv c, map_finSuccEquiv c). | **File**: `MvPowerSeries/Restricted/Distinguished.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma ×4
- **Statement**: skeletons `isDistinguishedX0_finSuccEquiv_symm`, `norm_finSuccEquiv_symm`, `isUnit_finSuccEquiv_symm_iff`, `finSuccEquiv_toMvRestrictedX0`.
- **Sketch**: decomposition D1–D4 (WPPrep_MV.lean:435–470 quotes): unfold + `RingEquiv.apply_symm_apply`; symm-isometry from Iso.lean:250; unit-iff via `isUnit_map_iff` or the legacy 2-liner.

### [T049] Mv transport dictionary II
- **Status**: done (2026-07-26) — D5–D8; coeff_toMvRestrictedX0 via hval (map_finSuccEquiv + eq_symm_apply) + coeff_finSuccEquiv_symm + congrArg-chain (mixed ↥-spelling forbids rw of coeff_map on the goal — term-mode composition instead); of_monic gained [NormOneClass R] (T-level NormOneClass needs it). | **File**: `MvPowerSeries/Restricted/Distinguished.lean` | **Depends on**: T048 | **Parallel**: no | **Type**: lemma ×4
- **Statement**: skeletons `norm_toMvRestrictedX0`, `toMvRestrictedX0_injective`, `coeff_toMvRestrictedX0`, `isDistinguishedX0_toMvRestrictedX0_of_monic`.
- **Sketch**: D5–D8 (quotes at :513–545, :1301–1310): injective = RingEquiv.injective ∘ `toRestricted_injective`; coeff via Iso.lean `coeff_finSuccEquiv_symm` (:64) + `map_finSuccEquiv` (:216), term-mode across seams; of_monic through the 1-var `isDistinguished_toRestricted_of_monic`.

### [CLEANUP-19] /cleanup on Distinguished.lean (final)
- **Status**: done (2026-07-26) — Distinguished.lean sorry-free, chain green. | **Depends on**: T049 | **Type**: cleanup (final per-file).

### [T050] Mv division bounds and quotient uniqueness
- **Status**: done (2026-07-26) — private finSuccEquiv_division_eq + three transports; RingEquiv map_mul fired fine (no quirk on equivs in the new tree). | **File**: `MvPowerSeries/Restricted/WeierstrassDivision.lean` | **Depends on**: T048 (uses dictionary) | **Parallel**: yes (with T052) | **Type**: lemma ×3
- **Statement**: skeletons `norm_q_le_of_eq_mul_add`, `norm_r_le_of_eq_mul_add`, `weierstrassDivision_q_unique`.
- **Sketch**: W1–W3 (quotes :654–707): push the division equation through Φ (term-mode `map_mul`/`map_add` — MonoidHomClass quirk site), apply the 1-var bounds/q_unique over `T`, pull norms back by the isometry, quotient equality by `(finSuccEquiv).injective`.

### [T051] hc-discharge over the Tate algebra
- **Status**: done (2026-07-26) — hunit-discharge ported; Mv norm_def needs (c := Fin.tail c) named arg (positional c-slot misparses); Fin.tail-vs-succ per-factor closed by trailing rfl. | **File**: `MvPowerSeries/Restricted/WeierstrassDivision.lean` | **Depends on**: T050 | **Parallel**: no | **Type**: lemma
- **Statement**: skeleton `exists_norm_inv_isUnit`.
- **Sketch**: W4 (quote :579–608): double attainment (1-var `exists_achievesGaussNorm` at `c 0`, Mv `exists_achievesGaussNorm` GaussNorm.lean:70), norm = explicit product of `K`-units via `map_prod (normHom)`, invert, constant via `C` + `norm_C` + `RingHom.isUnit_map`.

### [CLEANUP-20] /cleanup on Mv WeierstrassDivision.lean (final)
- **Status**: done (2026-07-26) — Mv WeierstrassDivision.lean sorry-free, chain green. | **Depends on**: T051 | **Type**: cleanup (final per-file).

### [T052] Mv mapAlgebra pack
- **Status**: done (2026-07-26) — congr-oneliner + iSup_congr isometry (IsRestricted is a plain Tendsto def in mathlib now). | **File**: `MvPowerSeries/Restricted/BaseChange.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma ×2
- **Statement**: skeletons `isRestricted_mapAlgebra`, `norm_mapAlgebra`.
- **Sketch**: B1–B2 (quotes :949–956 + the proven 1-var twins): cofinite-tendsto congr; `iSup_congr` + `coeff_map` + hiso.

### [T053] Splitting-isomorphism intertwining
- **Status**: done (2026-07-26) — legacy calc verbatim with new names; own-lemma call arity (c implicit here); finSuccEquiv_map raw intertwining private. | **File**: `MvPowerSeries/Restricted/BaseChange.lean` | **Depends on**: T052, T049 | **Parallel**: no | **Type**: lemma ×3 (+1 private)
- **Statement**: skeletons `coeff_finSuccEquiv_mapAlgebra` (+ private raw `finSuccEquiv_map` to add), `mapAlgebra_toMvRestrictedX0`, `isDistinguishedX0_mapAlgebra`.
- **Sketch**: B3–B5 (quotes :969–1035): raw intertwining by double ext + `coeff_coeff_finSuccEquiv`; Subtype.ext calc (term-mode); field-by-field `IsDistinguished` transport (unit via `RingHom.isUnit_map`, terms via isometry).

### [T054] Mv descend, retraction form
- **Status**: done (2026-07-26) — THE MV DESCEND (retraction form) + finite corollary. War stories recorded: (a) whnf-BOMB: isRestricted_retract's implicit d unified through Finsupp.prod pointwise — Fin.tail unfolded 1,020,667× (diagnostics); FIX: pin (d := ...) explicitly at every call; (b) set-with-subtype-lambda also pathological — body is set-free, 1-var style inline ⟨⟩; (c) omit-in-heavy-section triggered its own loop — privates moved to a minimal-variable RetractionCore section; (d) ring/linear_combination failed on proof-atom mismatch (X−X≠0 syntactically) — replaced by sub_add_sub_comm + defeq exact h10.symm; (e) map_mul rw quirk as documented — specific-term have hmm. CLEANUP-21 rides: file sorry-free, 2501 jobs. | **File**: `MvPowerSeries/Restricted/BaseChange.lean` | **Depends on**: T053, T050 | **Parallel**: no | **Type**: theorem (~110 LOC)
- **Statement**: skeleton `weierstrassDivision_descend_of_retraction` (finite corollary already written, compiles against it).
- **Sketch**: B6/G-G: the PROVEN 1-var `weierstrassDivision_descend_of_retraction` body with `Finsupp`-indexed coefficients: π coefficientwise (restrictedness by squeeze with the bound), `lmap_mul` clone over `Finsupp.antidiagonal`, retraction of the equation via `hπ`, difference killed by T050 bounds over L. Known traps carried in the artifact: `letI` for data instances; explicit `RingHom.map_mul` in the `linear_combination`.

### [CLEANUP-21] /cleanup on Mv BaseChange.lean (cadence + final)
- **Status**: done (2026-07-26) — Mv BaseChange.lean sorry-free (2501 jobs). | **Depends on**: T052, T053, T054 | **Type**: cleanup.

### [T055] Extension frame and hc-rung
- **Status**: done (2026-07-26) — both privates PROVEN first-compile. `extension_frame`: adjoin-all-roots inside `AlgebraicClosure K` (`IsAlgClosed.exists_pow_nat_eq` per radius), `Set.finite_range α` + `finiteDimensional_adjoin` for Module.Finite, spectral-norm letI pack (nontriviallyNormedField, ultrametric via `isNonarchimedean_spectralNorm`, `spectralNorm_extends` isometry, NormedSpace + `FiniteDimensional.complete`); generator norm via `pow_left_inj₀` on `hgen` (algebraMap-injective + `map_pow` + `IsScalarTower.algebraMap_apply` + rfl across the subtype seam). hc-rung: 1-var hunit division with T051 as witness, `NeBot (𝓝[≠] 0)` letI spelled `nhdsWithin (0:K) {(0:K)}ᶜ` + `NormedField.nhdsNE_neBot`, pulled back by `congrArg symm` + `map_add/map_mul/symm_apply_apply`. | **File**: `MvPowerSeries/Restricted/DivisibleRadius.lean` | **Depends on**: T051, T053 | **Parallel**: no | **Type**: private lemma ×2
- **Statement**: skeletons `extension_frame`, `weierstrassDivision_exists_of_forall_units`.
- **Sketch**: E1–E2 (quotes :1313–1358, :708–725): adjoin-all-roots spectral block (T030-pattern with `Set.finite_range` + `finiteDimensional_adjoin`); transport of the 1-var hunit division with T051 as the witness.

### [T056] Divisible base case
- **Status**: done (2026-07-26) — verbatim legacy composition: frame → `isDistinguishedX0_mapAlgebra`/`mapAlgebra` transport → hc-rung over L → `weierstrassDivision_descend` (finite corollary). Compiled with T057 in one pass. | **File**: `MvPowerSeries/Restricted/DivisibleRadius.lean` | **Depends on**: T055, T054 | **Parallel**: no | **Type**: private lemma
- **Statement**: skeleton `weierstrassDivision_exists_divisible`.
- **Sketch**: E3 (quote :1360–1374): frame → divide over L (hc-rung + B5-transport) → finite descend. The machine-checked legacy composition, verbatim shape.

### [T057] The radius-count induction
- **Status**: done (2026-07-26) — induction on N proven. Base: `Nat.card = 0` vs `Nonempty` contradiction (`Nat.card_pos.ne'`) ⇒ all-divisible ⇒ T056. Step: `not_forall.mp`, `Fact (0 < c i₀)` + `Fact (¬MemDVG)` haveI's, `L := GaussExtension K (c i₀)`; card-drop via `Fintype.card_lt_of_injective_of_notMem` (notMem spelling — `_not_mem` is gone) at `b := ⟨i₀, hi₀⟩`, injection `j ↦ ⟨j.1, j.2 ∘ memDivisibleValueGroup_of_base⟩`, injectivity needed bottom-up elaboration (`by have h2 := congrArg Subtype.val hab; exact h2` — a `show`-from form re-unifies α against the goal and fails), not-mem by `rintro ⟨⟨j, hj2⟩, hj⟩` + `subst` + `memDivisibleValueGroup_self`; IH at `omega`; descend via `weierstrassDivision_descend_of_retraction hiso GaussExtension.retraction retraction_algebraMap (Cπ := 1)` + `norm_retraction_le`. | **File**: `MvPowerSeries/Restricted/DivisibleRadius.lean` | **Depends on**: T056, T047, T046, T045 | **Parallel**: no | **Type**: private lemma
- **Statement**: skeleton `weierstrassDivision_exists_of_card_le`.
- **Sketch**: G-H: induction on N; base = all-divisible ⇒ T056; step: pick unrealised `i₀`, `L := GaussExtension K (c i₀)` under `Fact ¬MemDVG` (T047 field pack); `Nat.card` drop via `Nat.card_le_card_of_injective` on the inclusion (T045 monotonicity + self); IH over L on mapAlgebra'd data (T053); descend along `retraction` (T046, `Cπ = 1`) via T054. Universe: L stays in `Type u`.

### [CLEANUP-22] /cleanup on Mv DivisibleRadius.lean (cadence)
- **Status**: done (2026-07-26) — merged with CLEANUP-23 (same file, T055–T059 all landed before the pass): no debug remnants (`set_option`/`#print`/`sorry` scan clean), char-accurate 100-col check clean (earlier awk hits were unicode byte-count false positives), eta-golf on the `retraction_algebraMap` argument in T057; recompiled green. | **Depends on**: T055, T056, T057 | **Type**: cleanup.

### [CLEANUP-ALL-4] /cleanup-all before the unconditional milestones
- **Status**: done (2026-07-26) — ran post-milestone (milestones were proven in the same sitting): all development heads built green in one invocation (Mv Units + 1-var Complete + 1-var BaseChange + Mv DivisibleRadius, 2643 jobs); char-accurate 100-col sweep over the six tranche-4 files clean. | **Depends on**: CLEANUP-16, CLEANUP-18, CLEANUP-19, CLEANUP-20, CLEANUP-21, CLEANUP-22 | **Type**: cleanup-all.

### [T058] MILESTONE: Mv Weierstrass division at every radius
- **Status**: done (2026-07-26) — THE UNCONDITIONAL DIVISION TRIO, first-compile. exists = T057 at `N := Nat.card _` + `le_rfl` (term-mode); uniqueness = shipped 6-line shape with `toMvRestrictedX0_injective` + Mv `q_unique`; polynomial = monic-rescale mirror over `T = Restricted K (Fin.tail c)` (hg unfolded to the `toRestricted (c 0)` spelling via `unfold IsDistinguishedX0` + `finSuccEquiv_toMvRestrictedX0` rw, `hg'.isUnit_coeff`, `Nontrivial T` from `hg'.nontrivial`; `modByMonic_add_div`, `key`-lemma double-application). Axioms: standard only (stale-olean false alarm resolved by `lake build` before `#print axioms` — `lake env lean` does not refresh oleans). | **File**: `MvPowerSeries/Restricted/DivisibleRadius.lean` | **Depends on**: CLEANUP-ALL-4 | **Parallel**: no | **Type**: theorem ×3
- **Statement**: skeletons `weierstrassDivision_exists`, `weierstrassDivision_uniqueness`, `weierstrassDivision_polynomial` — NO radius hypotheses.
- **Sketch**: G-I: exists = T057 at `N := Nat.card _` (`le_refl`); uniqueness = exists + `toMvRestrictedX0_injective` + Mv `weierstrassDivision_q_unique` (the shipped 6-line shape, proven 3× at 1-var); polynomial = the twice-proven monic-rescale mirror over the comm ring `T` (keeps `hgs`; counterexample recorded).

### [T059] MILESTONE: Mv Weierstrass preparation at every radius
- **Status**: done (2026-07-26) — THE UNCONDITIONAL PREPARATION TRIO, first-compile. exists = 1-var `weierstrassPreparation_exists_of_forall_exists` over `(T, c 0)` with an `hdiv` oracle built from unconditional T058-exists pulled through `finSuccEquiv` both ways (defeq `IsDistinguishedX0` unfold feeds the 1-var hg directly); ω/e pulled back via `norm_toMvRestrictedX0`, `isUnit_finSuccEquiv_symm_iff`, `congrArg symm` + `map_mul` (symm∘toRestricted = toMvRestrictedX0 by defeq). unique = tranche-2 mirror: `Nontrivial T` by type-ascribed defeq `hg.nontrivial`, e-uniqueness by `NormMulClass (Restricted K c)` norm-cancellation vs `(c 0)^s ≠ 0`, ω-uniqueness by `degree_sub_lt` + Mv `norm_r_le_of_eq_mul_add` at `f := 0`. polynomial = mirror body (division-polynomial + q_unique ×3 + `isDistinguishedX0_toMvRestrictedX0_of_monic`). ULTIMATE GOAL LANDED: all six endpoints sorry-free, standard axioms, full build 2642 jobs. | **File**: `MvPowerSeries/Restricted/DivisibleRadius.lean` | **Depends on**: T058 | **Parallel**: no | **Type**: theorem ×3
- **Statement**: skeletons `weierstrassPreparation_exists`, `weierstrassPreparation_unique`, `weierstrassPreparation_polynomial` — NO radius hypotheses, no `hgs` on polynomial.
- **Sketch**: G-I: exists = the 1-var trick over `(T, c 0)` with T058-exists as oracle, pulled back through the dictionary (D1/D4/D5 + unit-iff); unique/polynomial = the tranche-2 mirror bodies with Mv ingredients (norm-cancellation vs `(c 0)^s ≠ 0`; `degree_sub_lt` + Mv `norm_r_le` at `f := 0`; division-polynomial + q_unique + of_monic).

### [CLEANUP-23] /cleanup on Mv DivisibleRadius.lean (final)
- **Status**: done (2026-07-26) — see CLEANUP-22 (single merged pass); file sorry-free, six endpoints `#print axioms` = standard three (checked against a FRESH olean — `lake build` before `#print axioms`, since `lake env lean` does not refresh oleans and a stale one reports phantom `sorryAx`). | **Depends on**: T059 | **Type**: cleanup (final per-file).

### [CLEANUP-FINAL-3] /cleanup-all on the whole development (tranche 4)
- **Status**: done (2026-07-26) — mechanical pass complete: every development head builds green (2643 jobs), tranche-4 files style-clean, six unconditional endpoints sorry-free on standard axioms. REMAINING FOR USER (naming only, flagged not decided): (a) 1-var `_of_field` suffix — keep or drop now that the Mv endpoints carry the plain names; (b) Mv `IsDistinguishedX0` / `Polynomial.toMvRestrictedX0` — keep or rename (e.g. `IsDistinguishedAt 0`). | **Depends on**: everything above | **Type**: cleanup-all (final). Includes the still-pending 1-var `_of_field` naming decision (user) and the Mv naming flags (IsDistinguishedX0 / toMvRestrictedX0).

### [POST-1] Post-completion refactor: oracle factoring + spectral unification + import hygiene
- **Status**: done (2026-07-26) — user-requested implementation of the audit findings. (a) `_of_exists`/`_of_forall_exists` factoring: new 1-var `weierstrassDivision_uniqueness_of_exists`; `weierstrassDivision_polynomial` GENERALISED (hunit + CompleteSpace + NeBot dropped — Euclidean division by the unit-rescaled monic divisor + hypothesis-free q-uniqueness, no oracle needed) and moved to the new OfExists section; new `weierstrassPreparation_{unique,polynomial}_of_forall_exists` in WeierstrassPrep; the hunit and `_of_field` endpoint quadruples are now one-line instantiations; the Mv division-polynomial/prep-unique/prep-polynomial mirrors replaced by `existsUnique_congr'`-transports through `finSuccEquiv` of the univariate factored theorems (Mv division-polynomial and its 1-var parent now completeness-free, `omit [CompleteSpace K]`). Net: each previously-triplicated body now has exactly one proof. (b) `MemDivisibleValueGroup.elim_finite_extension` (1-var DivisibleRadius.lean, root namespace, `[Finite ι]`-indexed) replaces both the Mv `extension_frame` and the inline single-root `K⟮α⟯` construction — the spectral-extension construction is done once; Mv DivisibleRadius drops the SpectralNorm/AlgebraicClosure imports. (c) Import hygiene: 1-var WeierstrassDivision imports Complete + Residue (+ the directly-used Polynomial.Div) instead of Units — the Units/PowerBoundedIso/TopologicallyNilpotentIso chain is out of the WP cone (still builds as its own head). WAR STORY: passing the section-parametrized private oracle `weierstrassDivision_forall_exists_tate` as a higher-order argument re-triggered the T054 Fin.tail whnf-bomb (meta-vs-meta unification of the implicit radius tuple); fix = pin `(K := K) (c := c)` at every call site. Gates: all heads 2643 jobs green, 17 endpoint/infrastructure declarations `#print axioms` = standard three, zero sorries. | **Type**: refactor.
