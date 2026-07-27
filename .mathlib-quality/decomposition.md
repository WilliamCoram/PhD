# Decomposition: Weierstrass division & preparation (Option B, Tranche 1)

## Skeleton location
Every lemma stated with `:= by sorry`; `lake build` passes (sorries only, no type errors) —
verified 2026-07-25.
- `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/Distinguished.lean` (5 sorries)
- `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/Rescale.lean` (12 sorries)
- `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/WeierstrassDivision.lean` (22 sorries)
- `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/WeierstrassPrep.lean` (5 sorries)

## Source situation (calibrates the adversarial pass)
The references are the project's own **machine-checked, sorry-free** Lean files:
`PhD/WeierstrassPrep/WeierstrassDivision.lean` (890 lines), `WPrep.lean` (444),
`WPrep_gen.lean` §0+§2 (lines 84–365).  "Verbatim source quote" therefore means the source
*declaration* at a `file:line` locator — its truth is certified by the compiler.  Attack
effort is concentrated on the statements that **differ** from the sources:
(G1) public statements generalised `1 → c`; (G2) `rescaleEquiv` generalised target `1 → c'`;
(G3) `contra` restated positively as `max ≤ ‖f‖`; (G4) density rerouted through
`AddSubgroup.dense_of_infDist_le`; (G5) the preparation unit-transport replaced by the new
`Units.lean` criterion; (G6) `[Nontrivial R]` dropped (implied by `NormOneClass`);
(G7) engine residue machinery re-pointed at the new `Residue.lean`.

Prior-B2 log: `.mathlib-quality/b2_log.jsonl` absent — no prior B2 history (checked).

---

## Architecture (binding)
- **Public API at general radius `c`** (`Fact (0 < c)`), no `c = 1`-labeled theorems:
  - bounds + uniqueness: *direct* weighted proofs, **no** `hα`/`hunit`;
  - existence + preparation: hypothesis `hα : ∃ u : Rˣ, ‖(u : R)‖ = c`, proof by
    `rescaleEquiv` conjugation into the engine.
- **Engine at radius 1** (implementation layer, documented as such): residue-monic reduction,
  ε-approximate division, dense + closed subgroup.  The residue ring of `T°` is polynomial
  only at radius 1 — this is why the engine lives there (module docstring records it).
- A future C-probe (T-PROBE ticket) may replace the engine by a direct weighted ε-division,
  deleting `hα`; the public statements would not change.

---

## File 1: Distinguished.lean

### L1.1 (leaf): `IsDistinguished` (structure — no sorry)
- Source (verbatim, WPrep_gen.lean:105–108, machine-checked):
  > structure distinguishedGen : Prop where
  >   unit : IsUnit (PowerSeries.coeff s f)
  >   norm_eq : PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f) * c ^ s
  >   norm_max : ∀ t, s < t → v (...coeff t f) * c ^ t < v (...coeff s f) * c ^ s
- Lean ↔ source: field-for-field transcription (renamed `isUnit_coeff/gaussNorm_eq/lt_of_gt`).
- Attacks: [1] edge `s = 0`: constant-term unit + dominance over all t ≥ 1 — matches source
  semantics ✓. [2] hypothesis-strength: `Semiring R` matches source §0 context ✓ minimal.
  [3] drift: none (transcription). SURVIVED.

### L1.2 (leaf): `IsDistinguished.ne_zero`
- Source: WPrep_gen.lean:128–129 (one-line proof from `unit.ne_zero`).
- Discharge: `IsUnit.ne_zero` + `map_zero` (mathlib, verified by source's own proof).
- Attacks: [1] needs `[Nontrivial R]` — source has it, kept ✓ (attack: drop it → `0 = 1`
  rings make `coeff s 0 = 0` a unit, statement false — hypothesis necessary). [2] edge f = 0
  direct contradiction ✓. [3] drift: none. SURVIVED.

### L1.3–L1.4 (leaves): `norm_coeff_mul_pow_eq`, `norm_pos`
- Source: WeierstrassDivision.lean:41–55 (`distinguished.norm_pos/norm_pos'`), weights
  restored per WPrep_gen §0.
- Discharge: `norm_def` + `gaussNorm_eq` field (L1.3); `gaussNorm_eq_zero_iff`
  (Restricted/GaussNorm.lean, general c) + `ne_zero` (L1.4).
- Attacks: [1] G1 generalisation `1 → c`: both are Gauss-norm identities already stated at
  general c in the new tree — the weighted field `gaussNorm_eq` is exactly `norm_def`-shaped ✓.
  [2] `norm_pos` edge: trivial S excluded by `[Nontrivial S]` ✓. [3] discharge check:
  `gaussNorm_eq_zero_iff` exists at `(hc : ∀ i, 0 < c i)`-analogue univariate (verified in
  GaussNorm.lean:113). SURVIVED.

### L1.5 (leaf): `IsDistinguished.C_mul`
- Source: WeierstrassDivision.lean:589–601 (`ext1`, c = 1, machine-checked), weights carried.
- Discharge: `Restricted.coeff_C_mul`-analogue = `MvPowerSeries.coeff_C_mul` via `val_mul`,
  `val_C` (new tree) + `norm_mul` + field-wise transcription of ext1's three parts.
- Attacks: [1] G1: each ext1 step multiplies both sides of a (in)equality by `‖a‖ > 0` — the
  `c ^ t` weights are spectators ✓ (checked per-field). [2] edge a = 1 ✓ identity.
  [3] discharge: `coeff_C_mul` verified present (mathlib line 424). SURVIVED.

### L1.6 (leaf): `isDistinguished_toRestricted_of_monic`
- Source: WPrep.lean:362–380 (`distinguished_of_monic`, c = 1), generalised: `‖ω‖ = 1` ↦
  `‖toRestricted c ω‖ = c ^ s`.
- Discharge: `Polynomial.coeff_coe`, `Monic.coeff_natDegree`,
  `Polynomial.coeff_eq_zero_of_natDegree_lt` (all mathlib, used by source's own proof).
- Attacks: [1] G1: the three fields at general c: unit ✓ (coeff s = 1); `gaussNorm_eq`
  becomes ‖g‖ = ‖coeff s‖·cˢ = 1·cˢ = hypothesis ωn ✓; `lt_of_gt` at t > s: coeff t = 0 so
  LHS = 0 < cˢ = RHS, needs `c ^ s > 0` ✓ Fact. [2] edge s = 0: ω monic degree 0 = 1?
  monic constants: ω = C 1; ωn : ‖1‖ = 1 ✓ holds. [3] drift: the c = 1 instance recovers the
  source statement verbatim (one_pow) ✓. SURVIVED.

---

## File 2: Rescale.lean

### L2.1 (leaf): `isRestricted_rescale`
- Source (verbatim, WPrep_gen.lean:174–180, machine-checked):
  > private lemma isRestricted_rescale {c₁ c₂ : ℝ} (a : R) (ha : ‖a‖ * c₂ = c₁) ...
  >   rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, ← ha, mul_pow]; ring
- Already general (c₁, c₂) in the source ✓ transcription.
- Discharge: `PowerSeries.coeff_rescale` (verified mathlib:567), `norm_mul`, `norm_pow`
  (NormMulClass), `Tendsto.congr`.
- Attacks: [1] typeclass: source context NormedCommRing (rescale needs CommSemiring —
  caught at skeleton build, fixed) ✓. [2] edge a = 0, c₂ arbitrary: ha forces c₁ = 0;
  IsRestricted at 0-weight — statement still true (rescale 0 f is coeff-0-concentrated) —
  vacuously fine, no positivity needed ✓ matches source (no Fact). [3] drift: none. SURVIVED.

### L2.2 (leaf): `norm_units_inv`
- Source: WPrep_gen.lean:183–188, hypothesis generalised from `‖u‖ = c` (with StrongPos) to
  `‖u‖ ≠ 0` (the only thing the proof uses).
- Discharge: `Units.mul_inv`, `norm_one`, `norm_mul`, `mul_left_cancel₀`.
- Attacks: [1] hypothesis-weakening attack (the point of the redesign): source's `0 < c` used
  only via `hc0.ne'` ✓ `‖u‖ ≠ 0` suffices. [2] `NormOneClass` needed for `norm_one` ✓ in
  section context. [3] name/namespace: root `_root_.norm_units_inv` — no mathlib clash
  (grepped). SURVIVED.

### L2.3 (group): `rescaleEquiv` + `rescaleEquiv_coe` + `rescaleEquiv_symm_coe`
- Source: WPrep_gen.lean:193–218, target radius generalised `1 → c'` (G2).
- Discharge: `PowerSeries.rescale`, `rescale_rescale`, `rescale_one` (mathlib, verified),
  `Units.mul_inv/inv_mul`, L2.1, L2.2.
- Attacks (G2): [1] forward leg: ‖u‖·c' = c ⇒ L2.1 with (a := u, c₁ := c, c₂ := c') ✓.
  inverse leg: need ‖u⁻¹‖·c = c': from L2.2, ‖u⁻¹‖ = ‖u‖⁻¹ = c'/c (Facts give ‖u‖ = c/c' ≠ 0)
  ✓ algebra checked. [2] edge c = c', u with ‖u‖ = 1 ✓; u = 1 gives identity ✓ (rescale_one).
  [3] composition: left/right inv via `rescale_rescale` — radius-independent ✓ verbatim.
  SURVIVED.

### L2.4 (leaf): `norm_rescaleEquiv`
- Source: WPrep_gen.lean:224–238 (`gaussNorm_rescale` + `norm_rescaleEquiv`), G2-generalised:
  `‖uᵏaₖ‖·c'ᵏ = ‖aₖ‖·cᵏ`.
- Discharge: `gaussNorm_eq` (ℕ-indexed sup, new tree) + `iSup_congr` + `coeff_rescale` +
  `norm_mul`/`norm_pow` + `mul_pow`.
- Attacks: [1] G2 identity: (‖u‖c')ᵏ = cᵏ ✓ from hu by mul_pow. [2] sup-congr valid for
  term-wise equal families ✓. [3] drift vs source: source is the c' = 1 instance ✓. SURVIVED.

### L2.5 (leaf): `isDistinguished_rescaleEquiv_iff`
- Source: WPrep_gen.lean:244–276 (`distinguished_rescaleEquiv`), now SYMMETRIC (both sides
  weighted) — the statement *simplifies* relative to the source.
- Discharge: L2.4-style coefficient identity `‖coeff k (rescale u f)‖·c'ᵏ = ‖coeff k f‖·cᵏ` +
  `Units.isUnit_units_mul` (source line 254) + field-wise transport.
- Attacks: [1] G2: unit-preservation is weight-independent ✓; norm fields transport by the
  coefficient identity ✓ both directions. [2] edge s = 0 ✓. [3] drift: at c' = 1 recovers
  the source's asymmetric statement through `distinguishedGen_one_iff`-content (weights at 1
  are invisible) ✓. SURVIVED.

### L2.6 (group): `Polynomial.coeff_comp_C_mul_X`, `comp_C_mul_X_comp_C_inv_mul_X`,
`degree_comp_C_mul_X_lt`
- Source: WPrep_gen.lean:280–339 (verbatim; pure polynomial algebra, machine-checked).
- Discharge: `Polynomial.induction_on'`, `monomial_comp`, `coeff_monomial` (mathlib; the
  source's own proof).
- Attacks: [1] mathlib-overlap attack: searched `Polynomial.comp` coeff API
  (`coeff_comp_...`) — no exact match found; keep. [2] edge k = 0 / p = 0 ✓. [3] namespace:
  now root `Polynomial.*` (public, was private) — no clash (grepped). SURVIVED.

### L2.7 (group): `rescaleEquiv_toRestricted`, `rescaleEquiv_symm_toRestricted`
- Source: WPrep_gen.lean:295–348, G2-generalised.
- Discharge: `Polynomial.coeff_coe`, L2.6, `RingEquiv.symm_apply_eq`.
- Attacks: [1] G2: statement radius-independent (coefficient computation) ✓. [2] seam: the
  `Subtype.ext`/`show`-based proof crosses the Restricted seam with term steps per
  [[restricted-seam-convention]] — source's own pattern ✓. SURVIVED.

---

## File 3: WeierstrassDivision.lean

### Public bounds (general c — G1+G3):

### L3.1 (leaf): `max_le_norm_of_eq_mul_add`
- Source (G3-restatement of, verbatim locator): WeierstrassDivision.lean:105–244 (`contra`:
  `... (hf_lt : ‖f‖ < max ‖g * q‖ ‖r‖) : False`), positive form `max ≤ ‖f‖` classically
  equivalent over ℝ.
- Source proof structure (mirrored): peak set of `q` finite & nonempty (restrictedness +
  attainment, lines 122–148) → largest peak `u` → dominant coefficient
  `‖coeff (u+s) (g*q)‖ = ‖g‖·‖q‖` by ultrametric sum with strict cross-term domination
  (lines 167–220) → `r` has no coefficient at `u + s` (line 222) → `‖g*q‖ ≤ ‖f‖` → both
  branches (lines 237–244).
- Discharge (new tree): achievers API — `exists_achievesGaussNorm`,
  `finite_setOfPred_achievesGaussNorm` (GaussNorm.lean, general c) replace the hand-rolled
  peak-set construction; `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (mathlib, source
  line 219) + `Finset.sup'_lt_iff` + `Nonempty.norm_sum_le_sup'_norm` for the sum; weights
  via `norm_le_iff` (general c).
- Attacks (G1 — the critical one): [1] weighted dominance: cross terms at (a,b), a+b = u+s:
  a < s ⇒ b > u ⇒ ‖coeff_b q‖·c^b < ‖q‖-achieved (strict, peak-max) and ‖coeff_a g‖·c^a ≤ ‖g‖;
  a > s ⇒ strict from `hg.lt_of_gt` (weighted!) and ≤ for q — the product of weighted terms
  telescopes since c^a·c^b = c^{u+s} ✓ (this is the same weight-bookkeeping as the
  now-proven `exists_achievesGaussNorm_dominant`; the argument generalises because every
  inequality used is weighted in the new predicate). [2] edge q = 0: handled first as in
  source ✓. [3] `r`-coefficient at u+s: `u + s ≥ s > deg r` — radius-free ✓.
  [4] G3 equivalence: `¬(x < y) ↔ y ≤ x` ✓ `not_lt`. SURVIVED.

### L3.2–L3.3 (leaves): `norm_q_le_of_eq_mul_add`, `norm_r_le_of_eq_mul_add`
- Source: WeierstrassDivision.lean:246–265, now corollaries of L3.1
  (`le_max_left/right` + `norm_mul` + division by `‖g‖ > 0` via L1.4).
- Attacks: [1] `‖g‖ > 0` from `norm_pos` needs Nontrivial — derived from NormOneClass (G6) ✓
  (mathlib `NormOneClass` ⇒ nontrivial, verified Basic.lean:782 comment). [2] arithmetic
  `‖g‖·‖q‖ ≤ ‖f‖ ⇒ ‖q‖ ≤ ‖g‖⁻¹‖f‖` field-free over ℝ ✓. SURVIVED.

### L3.4 (leaf): `weierstrassDivision_q_unique` (general c — moved from source's end)
- Source: WeierstrassDivision.lean:774–790: apply bounds at f := 0 to the difference.
- Discharge: L3.2 + `norm_le_zero_iff` + `toRestricted` sub/degree lemmas (new Basic).
- Attacks: [1] G1: the proof is bounds-only, hence general c immediately ✓ — this is the
  redesign's payoff case. [2] degree of r₁ - r₂ < s ✓ `degree_sub_le` + max_lt. SURVIVED.

### L3.5–L3.6 (leaves): `coeff_continuous`, `isClosed_setOf_coeff_eq_zero` (general c)
- Source: WeierstrassDivision.lean:486–502, weights added: `‖coeff v (g-f)‖·cᵛ ≤ ‖g-f‖` gives
  Lipschitz constant `c⁻ᵛ`.
- Discharge: `norm_le_iff` (general c) + `Metric.continuous_iff`; `IsSeqClosed.isClosed`.
- Attacks: [1] G1: constant `c^{-v}` positive (Fact) ✓ continuity survives any fixed factor.
  [2] source's ε-choice adapts: pick δ = ε·cᵛ ✓. SURVIVED.

### Engine (c = 1 — transcription with G7 re-pointing):

### L3.7 (group): `divisionAddSubgroup` fields
- Source: WeierstrassDivision.lean:276–288 (verbatim; `toRestricted_add/neg` now `map_add` /
  `map_neg` of the ring hom).
- Attacks: [1] degree of sums/negs ✓ source. [2] G7: `Polynomial.toRestricted` same name,
  now a ring hom — map-lemmas free ✓. SURVIVED.

### L3.8 (leaf): `exists_lt_one_forall_norm_coeff_le`
- Source: WeierstrassDivision.lean:293–318 (verbatim; `isRestricted_iff'` exists in new tree).
- Attacks: [1] F-empty branch ✓ source. [2] discharge names: `isRestricted_iff'` verified
  (univariate Basic:47). SURVIVED.

### L3.9 (leaf): `nontrivial_quotient_closedBall_ideal`
- Source: WeierstrassDivision.lean:327–333 / 431–434 (inline `haveI`s, now a lemma — G7
  improvement; `mem_closedBall_ideal` is the new-tree simp lemma).
- Attacks: [1] needs ‖1‖ = 1 (NormOneClass) ✓; ε < 1 essential (at ε ≥ 1 the quotient IS
  trivial — attack confirms hypothesis necessary). SURVIVED.

### L3.10 (leaf): `monic_residueRingHom_of_isDistinguished`
- Source: WeierstrassDivision.lean:322–350, G7: `Restricted.closedBall_residueRingHom` ↦
  `residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0)`;
  `pbCoeff` ↦ `powerBoundedCoeff`; `closedBall_residuePolynomial_coeff` ↦
  `coeff_residueRingHom` (rfl, Residue.lean:146).
- Attacks: [1] G7 name-map verified against Residue.lean (all three exist with matching
  shapes). [2] degree argument `degree_le_iff_coeff_zero` + `le_degree_of_ne_zero` ✓ source.
  SURVIVED.

### L3.11 (leaf): `exists_approx_div_of_monic_residue`
- Source: WeierstrassDivision.lean:357–374. G7 replacements: `Polynomial.exists_div_by_monic`
  ↦ mathlib `Polynomial.modByMonic_add_div` + `degree_modByMonic_lt`;
  `Polynomial.liftQuot` (Polylift) ↦ mathlib `Polynomial.lifts_and_degree_eq` over the
  surjection `Ideal.Quotient.mk` (membership in `lifts` via `Polynomial.lifts_iff_set_range` +
  `Polynomial.map_surjective`); `pbPoly_to_pbRestricted` ↦ `toPowerBounded`;
  `closedBall_residueRingHom_pbPoly_to_pbRestricted` ↦ `residueRingHom_toPowerBounded`;
  `closedBall_norm_le_of_residueRingHom_eq_zero` ↦
  `(residueRingHom_closedBall_ideal_eq_zero_iff hε0 _).mp`.
- Attacks: [1] the lifts-route: `lifts_and_degree_eq` gives a lift with EQUAL degree — the
  source only needed ≤ ✓ stronger is fine. [2] iff-direction of the kernel lemma: need
  norm ≤ ε FROM residue-zero — that is the `.mp` direction of the new iff ✓ (Residue.lean:154
  gives `= 0 ↔ ‖f.1‖ ≤ ε`). [3] nontriviality of the quotient supplied by L3.9 via `haveI` ✓.
  SURVIVED.

### L3.12 (leaf): `exists_mem_divisionSet_norm_le`
- Source: WeierstrassDivision.lean:386–467 (the 80-line scaling argument, verbatim transport;
  `C_mul_toRestricted` from old ResC ↦ new-tree `map_mul`-of-`toRestricted` composed with
  `Restricted.C` — the identity `C c a * toRestricted c r = toRestricted c (C a * r)` is
  `(toRestricted c).map_mul` + `toRestricted_C` ✓ available).
- Attacks: [1] the norm bookkeeping is radius-free at c = 1 (engine) — transcription ✓.
  [2] G7 names checked: `norm_C`, `coeff_C_mul` (via val), `isPowerBounded_of_norm_le_one` ✓.
  SURVIVED.

### L3.13 (leaf): `dense_divisionSet` (G4)
- Source: WeierstrassDivision.lean:469–483, rerouted: `SeminormedAddGroup.epsilonDense` +
  `dense_epsilonDense` (deleted EpsilonDense.lean) ↦ `AddSubgroup.dense_of_infDist_le`
  (ForMathlib/Topology/MetricSpace/HausdorffDistance.lean:17, BGR 1.1.4/2, `to_additive`).
- Bridge: for f ≠ 0, L3.12 gives b ∈ H with `‖-f + b‖ ≤ ε‖f‖`; then
  `infDist f H ≤ dist f b = ‖f - b‖ = ‖-f + b‖ ≤ ε‖f‖ = ε · dist f 0`; for f = 0,
  `infDist 0 H = 0` (0 ∈ H).
- Attacks: [1] G4 instance: `dense_of_infDist_le` needs `IsIsometricVAdd G G` — for a
  seminormed add comm group translation is an isometry; mathlib instance
  (`Mathlib.Topology.MetricSpace.IsometricSMul`) — VERIFY-AT-TICKET (flagged in ticket; if
  missing, a 2-line local instance from `dist_add_left`). [2] ‖f - b‖ = ‖-f + b‖ via
  `norm_sub_rev`-style ✓. [3] ε ∈ (0,1) from L3.8 ✓. SURVIVED (one flagged verify).

### L3.14 (leaf): `isClosed_divisionSet`
- Source: WeierstrassDivision.lean:504–574 (verbatim; the Cauchy-extraction via bounds).
  Note: source builds the limit polynomial by hand (lines 545–569, flagged "almost certainly
  a better way") — port as-is; golfing is CLEANUP's job.
- Discharge: L3.2/L3.3 (bounds — now general-c lemmas applied at c = 1),
  `cauchySeq_tendsto_of_complete`, L3.6, `tendsto_nhds_unique`.
- Attacks: [1] bounds at c = 1 instance of general lemmas — weights `1^k` need `one_pow`
  simp-bridging at application ✓ (same pattern as Units.lean's c = 1 uses). [2] completeness
  of Restricted ✓ (Complete.lean). SURVIVED.

### L3.15 (leaf): `weierstrassDivision_exists_of_norm_eq_one`
- Source: WeierstrassDivision.lean:578–586 (verbatim 4-liner: closure of dense-closed set).
- Attacks: [1] `IsClosed.closure_eq` + `Dense.closure_eq` ✓. SURVIVED.

### Public existence (general c — G1 via rescale):

### L3.16 (leaf): `weierstrassDivision_exists`
- Source: composition of WeierstrassDivision.lean:757–769 (the `C a * g` normalisation) and
  WPrep_gen.lean §3's transport pattern (367–373: "Proofs: transport along
  Restricted.rescaleEquiv").
- Sketch: obtain u from hα; e := rescaleEquiv u (hu·1 = c form); transport hg by L2.5, h and
  hunit by isometry (WPrep_gen.lean:353–363 `hunit_transport` verbatim); apply L3.15-chain at
  radius 1 (with the `C a`-normalisation of :757); pull q back by e.symm and r by
  `rescaleEquiv_symm_toRestricted` (degree preserved by `degree_comp_C_mul_X_lt`).
- Attacks: [1] the transported g is distinguished at 1 with ‖·‖ = possibly ≠ 1 — the
  norm-eq-one reduction happens INSIDE via :757's `C a` trick with transported h ✓ mirrors
  source composition. [2] equation transport: e is a ring iso, so f = g·q + r pulls back
  through e.symm term-by-term with `rescaleEquiv_symm_toRestricted` ✓. [3] edge c = 1,
  u = 1: rescaleEquiv = identity-ish (rescale_one) — statement degenerates to the engine ✓.
  SURVIVED.

### L3.17 (leaf): `weierstrassDivision_uniqueness`
- Source: WeierstrassDivision.lean:792–803 (assembly of L3.16 + L3.4 + remainder
  cancellation) — general c since both ingredients are.
- Attacks: [1] shared-witness nested ∃! kept as in source (documented exception:
  statement-splitting — parts available as L3.16/L3.4). SURVIVED.

### L3.18 (leaf): `weierstrassDivision_polynomial`
- Source: WeierstrassDivision.lean:829–888 (monic Euclidean division in R[X] + uniqueness
  bridging; counterexample docstring for `hgs` preserved).
- Attacks: [1] G1: the R[X]-division half is radius-free; the uniqueness half uses L3.17 at
  c ✓. [2] `hgs` necessity: source's ℤ_p counterexample survives at c = 1 instance —
  documented ✓. SURVIVED.

---

## File 4: WeierstrassPrep.lean

### L4.1 (leaf): `norm_toRestricted_X_pow_sub` (general c)
- Source: WPrep.lean:152–163 (`test5`, c = 1), weights restored: value `c ^ s`, hypothesis
  `‖r‖ ≤ c ^ s`.
- Discharge: `norm_monomial` (general c, GaussNorm) via `toRestricted_monomial`/`map_pow` +
  `IsUltrametricDist.norm_add_le_max` + `le_gaussNorm` at index s.
- Attacks: [1] G1: upper bound max(cˢ, ‖r‖) = cˢ ✓; lower bound: coeff s of X^s − r is 1
  (`deg r < s` kills r's coeff; mathlib `Polynomial.monic_X_pow_sub` neighbourhood), Gauss
  term ‖1‖·cˢ = cˢ ✓. [2] mathlib-overlap: `monic_X_pow_sub` (verified, Monic.lean:427)
  discharges the old test1–4 entirely — they are NOT ported (deleted duplication). SURVIVED.

### L4.2 (leaf): `weierstrassPreparation_exists_of_norm_eq_one` (engine, c = 1; G5)
- Source: WPrep.lean:178–309 (machine-checked). Structure mirrored: divide X^s by g
  (L3.15-chain) → ω := X^s − r → g·e' = ω → norms → **unit-ness of e'**.
- G5 redesign of the unit-ness block (source lines 196–303): keep the residue-degree
  arithmetic (σG·σE = σW in `Polynomial (R°⧸I)`, degrees s + deg σE = s ⇒ σE a constant
  unit; source lines 201–293) but run it at `I := PowerBounded.topologicalNilradical ℤ`
  (equal to the source's openBall-1 ideal by `topologicalNilradical_eq_ball_ideal_one`) using
  the new `residueRingHom` + `coeff_residueRingHom`; then CONCLUDE by the general unit
  criterion: σE constant-unit gives `pbCoeff E 0` unit in `R°⧸R°°` ⇒ unit in `R°`
  (`isUnit_iff_isUnit_mk_topologicalNilradical`) ⇒ `‖coeff 0 e'‖ = 1` (units of R° have norm
  1) and higher coefficients in the nilradical ⇒ topnil ⇒ `‖coeff t e'‖ < 1`; then
  `PowerSeries.Restricted.isUnit_iff` (Units.lean, general radius, ⇐ direction) yields
  `IsUnit e'` directly — no `T°`-unit detour, no `openBall_ideal_isUnit_iff`, no
  `isUnit_subring_iff`.
- Attacks (G5): [1] does σE-constant-unit still follow? — the degree arithmetic uses only
  ring/degree lemmas over the quotient (natDegree_mul', leadingCoeff_mul', eq_C_of_degree_le_zero)
  — ideal-independent ✓. [2] ‖coeff 0 e'‖ = 1 step: unit u of R° has ‖u‖·‖u⁻¹‖ = 1 with both
  ≤ 1 ⇒ ‖u‖ = 1 — 3-line argument, no gap ✓. [3] dominance for isUnit_iff needs STRICT
  `‖coeff t e'‖ < ‖coeff 0 e'‖ = 1` ∀ t ≠ 0 — from σE constant: coeffs t ≥ 1 of σE vanish ⇒
  pbCoeff E t ∈ nilradical ⇒ topnil ⇒ norm < 1 ✓ (`mem_topologicalNilradical_iff` +
  `isTopologicallyNilpotent_iff_norm_lt_one`). [4] fallback documented: if the assembly
  fights, the `isUnit_powerBounded_iff` T°-route is equivalent (both proven). SURVIVED.

### L4.3 (group): `weierstrassPreparation_exists` + `weierstrassPreparation_unique`
  (general c)
- Source: WPrep.lean:316–359 (descale by hunit g; uniqueness via bounds), composed with the
  §2 transport and the monic renormalisation `u ^ s` (WPrep_gen.lean:372–373: "a monic ω of
  degree s at parameter 1 pulls back to ω(u⁻¹x) with leading coefficient u⁻ˢ; renormalise by
  uˢ").
- Sketch (exists): rescale g to radius 1 (L2.3/L2.5, hunit transported), apply L4.2-chain
  (via WPrep.lean:316's `C a` normalisation), obtain ω₁ monic deg s at 1 and unit e₁; pull
  back: ω := C(uˢ)·(ω₁.comp (C u⁻¹ · X)) is monic of degree s (leading coeff uˢ·u⁻ˢ = 1;
  `coeff_comp_C_mul_X`), ‖toRestricted c ω‖ = cˢ (isometry + L4.1-style), e := e.symm-image
  adjusted by C(u⁻ˢ) stays a unit; equation transports through the ring iso.
- Attacks: [1] the u^s-renormalisation: coeff k of ω₁.comp(C u⁻¹ X) is u⁻ᵏ·coeff k ω₁ (L2.6);
  at k = s: u⁻ˢ·1; multiplying by C(uˢ): coeff s = 1 ✓ monic; degree preserved
  (`degree_comp_C_mul_X` ≤-form + leading ≠ 0) ✓. [2] norm: ‖toRestricted c ω‖ — the
  rescale isometry sends toRestricted 1 ω₁ (norm 1) to the c-side BEFORE the C(uˢ)-twist;
  ‖C(uˣ)‖-factor: ‖uˢ‖ = cˢ ✓ bookkeeping closes: ‖ω‖_c = ‖uˢ‖·‖symm(ω₁)‖ = cˢ·1 ✓.
  [3] uniqueness at general c: via L3.4 (bounds, already general) mirroring WPrep.lean:332
  ✓ no transport needed. SURVIVED.

### L4.4 (leaf): `weierstrassPreparation_polynomial` (general c)
- Source: WPrep.lean:410–444 (bridging via `weierstrassDivision_polynomial` +
  `isDistinguished_toRestricted_of_monic` — both general-c leaves here).
- Attacks: [1] all ingredients general-c by this point ✓ assembly radius-uniform.
  [2] ∃!∃! shared-witness exception documented as in L3.17. SURVIVED.

---

## API gaps
None.  Every leaf discharges from mathlib (verified names), the new ForMathlib tree
(Residue/Units/GaussNorm/achievers — all sorry-free, standard axioms), or the machine-checked
legacy sources being ported.  The single flagged verify-at-ticket item is the
`IsIsometricVAdd` instance for L3.13 (2-line local fallback identified).

## Confidence gate
1. every leaf discharged/cited ✓ (above)   2. skeleton compiles, sorries only ✓
3. verbatim source locators per leaf ✓ (machine-checked Lean sources)
4. adversarial pass per leaf ✓ (focused on G1–G7 redesigns; transcriptions inherit
   compiler-certified truth at their source radius)   5. prior-B2 log: empty ✓
6. tree mirrors the sources' own lemma structure ✓ (locators above; LOC anchors: contra 140
   source lines → L3.1; divApprox 80 → L3.12; prep-norm-one 130 → L4.2)
7. single-conclusion: multi-part sources split (bounds q/r separate; monic∧degree kept as one
   leaf L3.10 — shared derivation, assembly-style, justified; ∃!∃! forms are shared-witness
   exceptions, documented at L3.17/L4.3/L4.4)
GATE: PASS.

---

# Tranche 2 decomposition notes (2026-07-25)

Skeletons: `BaseChange.lean`, `DivisibleRadius.lean`, + `weierstrassPreparation_exists_of_forall_exists`
(WPrep), `exists_lt_one_forall_norm_coeff_mul_pow_le` (WDiv). `lake build` green, 24 sorries.

## New-mathematics leaves (no legacy Lean; prose proofs, verified in-session)

### The prep-as-corollary trick (T025)
Divide `X^s` by `g`: `X^s = g·q + r`, `deg r < s`; set `ω := X^s − r`, monic of degree `s`
(coefficient block), `‖ω‖ = c^s` (`norm_r_le` + `norm_toRestricted_X_pow_sub`), distinguished
(T003). Divide `g` by `ω`: `g = ω·P + S`, `deg S < s`. Substituting `ω = g·q`:
`g = g·(q·P) + S`. Comparing with `g = g·1 + 0` by the hypothesis-free
`weierstrassDivision_q_unique`: `q·P = 1`, so `P` is a unit and multiplying `g·q = ω` by `P`
gives `g = P·ω`. Structural precedent: mathlib's adic `WeierstrassPreparation` (preparation
from division). Consumes only shipped general-`c` lemmas; no completeness needed beyond the
division-existence hypothesis.

### The no-tie lemma (T036)
If `‖aₜ‖c^t = ‖aₛ‖c^s` with `t < s` and `aₛ = ↑u` a unit, then
`c^(s−t) = ‖aₜ‖·‖aₛ‖⁻¹ = ‖aₜ·↑u⁻¹‖` (`norm_mul`, `norm_units_inv`), so
`MemDivisibleValueGroup R c` with `n = s − t ≠ 0`. Contrapositive: off the divisible closure
the dominant term of a distinguished series strictly dominates every other Gauss term
(`t > s` is already strict by `lt_of_gt`; `≤` for all `t` from `gaussNorm_eq`).

### The one-step contraction division (T034)
Source: BGR §5.2.1 Prop 2 / §5.2.2 Thm 1 (successive-approximation division) — this leaf is
its induction step, quantified as: with `u` the unit `s`-coefficient of `g`,
`qf := u⁻¹·(s-shift of f)` (restricted: shifted null Gauss terms times a constant) and
`rf := trunc s f`, the identity `monomial s (↑u)·qf = f − rf` gives
`-f + (g·qf + rf) = (g − monomial s ↑u)·qf`, whose norm is
`‖g − monomial s ↑u‖·‖qf‖ ≤ (θ·M)·(M⁻¹·‖f‖) = θ·‖f‖` by norm multiplicativity,
`norm_le_iff` coefficient bounds, and `θ` from T033. Density then follows by
`AddSubgroup.dense_of_infDist_le` (BGR 1.1.4/2) exactly as in the shipped radius-1 engine,
and existence by closed (T024) + dense.

### Rejected route (recorded): density + limits
Approximating divisions at `cₖ ↑ c` are coherent (q-uniqueness) — a single power series
`q̂` — but `q̂ ∈ ⋂ₖ Restricted K cₖ` with bounded Gauss terms at `c` does not give
`q̂ ∈ Restricted K c` (shape `Σ c⁻ᵗXᵗ`: all Gauss terms `≡ 1`). The dichotomy above avoids
the missing-decay obstruction entirely.

## Ported leaves (machine-checked legacy source, WPrep_gen.lean at this pin)
- mapAlgebra pack: :910–949. Distinguishedness transport: :954–980 (fields for
  unit-reflection). Descent: :985–1117 (retraction + hypothesis-free bounds kill the
  difference). Divisible-radius division: :1195–1244 (spectral-norm extension block);
  uniqueness/polynomial: :1246–1314. `exists_norm_inv_isUnit`: :884–899.
  `MemDivisibleValueGroup`: :869 (def verbatim).
- NOT ported (dead under prep-as-corollary): `isUnit_of_isUnit_mapAlgebra` (:1121–1175),
  §5 prep-descent (:1316–1626) — replaced by the trick at each generality.

---

# Tranche 3 decomposition (2026-07-25): Multivariate Weierstrass division & preparation

## Goal (pinned with user this session)

Weierstrass division and preparation for `MvPowerSeries.Restricted K c`,
`c : Fin (n+1) → ℝ`, series distinguished in `X 0`, over a complete nontrivially normed
ultrametric field `K`, in **two public régimes**:

1. **divisible radii** — `∀ i, MemDivisibleValueGroup K (c i)` (legacy-backed port);
2. **free head radius** — `¬MemDivisibleValueGroup (Restricted K (Fin.tail c)) (c 0)`
   (new mathematics via the tranche-2 dichotomy; NO hypothesis on the tail radii).

The unit-realised-radii régime (`hc : ∀ i, ∃ u : Kˣ, ‖u‖ = c i`) is an **internal private
rung** (user decision; `hc ⇒` per-coordinate divisible with `m = 1`, so public hc-endpoints
would repeat the 1-variable redundancy pruned earlier today). Full every-polyradius
(mixed dependent radii, e.g. `c 0 = c 1` both off the divisible closure) requires the
annulus/Gauss-point field — explicitly OUT of scope (future tranche; needs its own
API-gap sub-decomposition with classical sources).

## Skeleton location (Step 2.5 — verified)

- `PhD/ForMathlib/RingTheory/MvPowerSeries/Restricted/Distinguished.lean` (2 real defs + 8 sorries)
- `PhD/ForMathlib/RingTheory/MvPowerSeries/Restricted/WeierstrassDivision.lean` (4 sorries)
- `PhD/ForMathlib/RingTheory/MvPowerSeries/Restricted/BaseChange.lean` (1 real def + 1 rfl lemma + 6 sorries)
- `PhD/ForMathlib/RingTheory/MvPowerSeries/Restricted/DivisibleRadius.lean` (14 sorries)

`lake build PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.DivisibleRadius` ✓
(2637 jobs, warnings = sorries only, no type errors) — verified 2026-07-25.
The two anchor defs (`IsDistinguishedX0`, `Polynomial.toMvRestrictedX0` as a `RingHom`
composition) and `mapAlgebra` + `val_mapAlgebra (rfl)` elaborate for real — the dependency
shape of the whole tree type-checks.

## Source situation (calibrates the adversarial pass)

**Primary source: `PhD/WeierstrassPrep/WPPrep_MV.lean` (1810 lines).** Compiles at this pin
(2614 jobs). **CAVEAT found by the source-trust attack:** its endpoints depend on `sorryAx`
(`#print axioms mvWeierstrassDivision_existance_divisible` = `[propext, sorryAx,
Classical.choice, Quot.sound]`) through six sorried support lemmas in the legacy ToPR tree.
The *composition structure* (§§0–5: transport, discharge, endpoints, base change, descent)
is machine-validated; the sorried analytic support maps 1-to-1 onto **proven, sorry-free**
new-tree declarations:

| sorried legacy support | proven new-tree replacement |
|---|---|
| `MvRestricted.bar` (ToPR/MvRestricted.lean:147, dominant product term) | `MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant` + `NormMulClass` instance (Mv GaussNorm.lean:249) |
| `NormOneClass` local instance (Restricted_powerbounded_topnil.lean:148) | `NormOneClass` instance (Mv GaussNorm.lean:237) |
| Gauss norm of a monomial ×2 (ibid.:81/202) | `norm_monomial` (Mv GaussNorm.lean:220) |
| `achievingPoints_finite` (ToPR/Restricted.lean:172) | `finite_setOfPred_achievesGaussNorm` (Mv GaussNorm.lean:83) |
| `isRestricted_monomial` detail (ToPR/Restricted.lean:326) | `isRestricted_monomial` (1-var Basic.lean, proven) |

**The port therefore CLOSES the legacy trust gap**: every leaf below discharges from the
sorry-free new tree; nothing imports the ToPR/legacy files.

**Secondary source (free-head-radius régime — new mathematics):** the tranche-2 project
declarations, all sorry-free and axiom-checked standard this session:
`forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup` (1-var DivisibleRadius.lean,
general `R`), `weierstrassDivision_exists_of_forall_lt` (1-var WeierstrassDivision.lean,
general `R`), `weierstrassPreparation_exists_of_forall_exists` (1-var WeierstrassPrep.lean,
general `R`). Prose proof per new leaf below (tranche-2 precedent for in-session prose).

Convention (tranche-1/2 precedent): for machine-checked Lean sources, the **verbatim quote
is the legacy Lean statement**, cited by exact line number at this pin.

## Architecture (binding)

- File map mirrors the 1-variable layer exactly: `Distinguished` → `WeierstrassDivision`
  (unit-free core) → `BaseChange` (mapAlgebra + descent) → `DivisibleRadius` (endpoints).
- `IsDistinguishedX0` and `Polynomial.toMvRestrictedX0` are DEFINED by transport along
  `finSuccEquiv` (legacy §0 convention); intrinsic slice unfoldings deferred until a
  consumer needs them (legacy deferred them too).
- `toMvRestrictedX0` is a `RingHom` ((finSuccEquiv).symm ∘ toRestricted (c 0)) —
  improvement over legacy (bare def + 5 hand-proved simp lemmas): map_zero/one/add/sub/mul
  come free from the RingHom API.
- Preparation in each régime is the 1-variable trick
  `weierstrassPreparation_exists_of_forall_exists` instantiated over `(T, c 0)` and pulled
  back; NO intermediate prep rungs, NO unit-descent lemma.
- Instance package for `T = Restricted R (Fin.tail c)`: ALL already instances in the new
  tree (NormedCommRing via Basic.lean:98 / GaussNorm; NormMulClass GaussNorm.lean:249;
  NormOneClass :237; IsUltrametricDist :245; NeBot :268; CompleteSpace Complete.lean:89 at
  GENERAL index type — legacy's Fin-induction workaround vanishes). Legacy §1 contributes
  ZERO leaves.

**Deviations from the legacy source (each justified — rule 4 audit):**
1. `exists_unit_norm_tate` (hα-discharge, legacy :569) NOT ported: the tranche-1 1-variable
   API eliminated the `hα`/`h` hypotheses; only `hunit` remains.
2. `isUnit_of_isUnit_mapAlgebraMv` (legacy :1247) NOT ported: legacy needed it because its
   §5 prep descended a unit; the trick builds the unit at `K`-level from q-uniqueness
   (same supersession as 1-variable tranche 2).
3. `MvRestricted.mapAlgebra_injective` (legacy :957) NOT ported: no consumer in the new
   architecture (descend uses norms and bounds, not injectivity).
4. Legacy §1 instance section NOT ported (all instances exist); `Nontrivial T` (legacy
   :325) also dropped — the 1-variable theorems derive nontriviality from
   `IsDistinguished.nontrivial`, never from an instance.
5. Legacy §6 consistency test / `congrBase` (:1678–1810) DEFERRED: the new architecture
   makes it moot (the 1-variable theorems are already stated over general `R`; the `n = 0`
   collapse adds no information).
6. hc-endpoints (legacy §4 six, :708–931) demoted to ONE private existence rung.
7. Division-polynomial endpoints KEEP `hgs : g₀.degree ≤ s` (necessary — the 1-variable
   counterexample `X^s + p•X^(s+1)` over `ℤ_p` transports); prep-polynomial endpoints have
   NO `hgs` (matches legacy :846/:1602 and the tranche-2 finding).

**Naming flags for ticket time** (bikeshed, not blocking): `IsDistinguishedX0`,
`toMvRestrictedX0`, `_of_not_memDivisibleValueGroup` suffix; also the pending 1-variable
`_of_field` rename interacts with Mv naming.

## File 1: Distinguished.lean

Context: `{R} [NormedCommRing R] [IsUltrametricDist R] {n} {c : Fin (n+1) → ℝ}
[Fact (∀ i, 0 < c i)]`. Anchor defs are real (compile); 8 leaves.

- **D1** (leaf): `isDistinguishedX0_finSuccEquiv_symm` — Distinguished.lean:56
  - Source: WPPrep_MV.lean:435–442 (`distinguishedMvGen_finSuccEquiv_symm`)
  - Quote: > "lemma distinguishedMvGen_finSuccEquiv_symm … distinguishedMvGen n c
    ((MvRestricted.finSuccEquiv R n c).symm x) s ↔ distinguishedGen norm (c 0) x.1 s := by
    unfold distinguishedMvGen; rw [RingEquiv.apply_symm_apply]"
  - Match: identical statement, new-tree names (`IsDistinguished` for `distinguishedGen`,
    new `finSuccEquiv`); proof = unfold + `RingEquiv.apply_symm_apply`.
  - Discharge: mathlib `RingEquiv.apply_symm_apply` (in use by compiled legacy at this pin
    and by new-tree Iso.lean).
  - Attacks: [source-drift] legacy proof is 2 lines, definitional — no drift possible;
    [edge] `s = 0`, `x = 0`: pure Prop-transport, nothing to fail; [discharge]
    apply_symm_apply verified in use. SURVIVED.
  - LOC: legacy 8 → ~8. Prior-B2: clean (0-entry log).

- **D2** (leaf): `norm_finSuccEquiv_symm` — Distinguished.lean:63
  - Source: WPPrep_MV.lean:449–456; Quote: > "have h := MvRestricted.norm_finSuccEquiv n c
    ((…).symm x); rw [RingEquiv.apply_symm_apply] at h; exact h.symm"
  - Match/Discharge: from new-tree `norm_finSuccEquiv` (Iso.lean:250, PROVEN — legacy's
    version was a restatement of the ToPR isometry; new tree already has it).
  - Attacks: [discharge] Iso.lean:250 read this session, exact statement
    `‖finSuccEquiv R c f‖ = ‖f‖` ✓; [drift] 3-line symm-juggle, none; [hypothesis] no
    NormMulClass needed — pure isometry. SURVIVED. LOC ~5. Prior-B2 clean.

- **D3** (leaf): `isUnit_finSuccEquiv_symm_iff` — Distinguished.lean:70
  - Source: WPPrep_MV.lean:458–463; Quote: > "⟨fun h => by simpa using h.map (…), fun h =>
    h.map (….symm)⟩"
  - Discharge: mathlib `isUnit_map_iff` (Units/Equiv.lean, MulEquivClass) or the legacy
    2-line `IsUnit.map` both ways.
  - Attacks: [discharge] `isUnit_map_iff` located at this pin (Units/Equiv.lean:206
    region); RECORDED RISK: the recurring MonoidHomClass-synthesis quirk on opaque
    Restricted may block the one-liner — fallback is the legacy 2-line term proof, which
    compiled; [drift] none; [edge] trivial unit `1` ✓. SURVIVED. LOC ~4. Prior-B2 clean.

- **D4** (leaf): `finSuccEquiv_toMvRestrictedX0` — Distinguished.lean:100
  - Source: WPPrep_MV.lean:467–470; Quote: > "MvRestricted.finSuccEquiv R n c
    (Polynomial.toMvRestrictedX0 n c ω) = Polynomial.toRestricted (c 0) ω :=
    (MvRestricted.finSuccEquiv R n c).apply_symm_apply _"
  - Match: with `toMvRestrictedX0` now a RingHom composition the proof is still
    `apply_symm_apply` (possibly through `RingHom.comp_apply` unfolding).
  - Attacks: [composition] the new def is defeq to legacy's (symm applied to toRestricted)
    — skeleton elaboration proves the types line up; [drift] none; [discharge] verified.
  - SURVIVED. LOC ~4. Prior-B2 clean.

- **D5** (leaf): `norm_toMvRestrictedX0` — Distinguished.lean:107
  - Source: WPPrep_MV.lean:513–517; Quote: > "‖toMvRestrictedX0 n c ω‖ =
    ‖toRestricted (c 0) ω‖ := MvRestricted.norm_finSuccEquiv_symm n c _"
  - Discharge: D2. Attacks: [composition: D2 true ⇒ D5 by rfl-shape] ✓; [drift] none;
    [edge ω = 0] both sides 0 ✓. SURVIVED. LOC ~3. Prior-B2 clean.

- **D6** (leaf): `toMvRestrictedX0_injective` — Distinguished.lean:111
  - Source: WPPrep_MV.lean:518–524; Quote: > "fun ω₁ ω₂ h => by have h1 := congrArg
    (MvRestricted.finSuccEquiv R n c) h; rw [finSuccEquiv_toMvRestrictedX0, …] at h1;
    exact coe_inj.mp (congrArg Subtype.val h1)"
  - Discharge: D4 + 1-var `Polynomial.toRestricted_injective` (proven, Basic.lean:215) —
    cleaner than legacy's coe_inj route: injective RingEquiv ∘ injective toRestricted.
  - Attacks: [composition] Function.Injective.comp of two proven injectives — 1-line;
    [drift] statement identical; [discharge] both cited decls read this session. SURVIVED.
  - LOC legacy 7 → ~3. Prior-B2 clean.

- **D7** (leaf): `coeff_toMvRestrictedX0` — Distinguished.lean:119
  - Source: WPPrep_MV.lean:528–545; Quote: > "MvPowerSeries.coeff t (toMvRestrictedX0 n c
    ω).1 = MvPowerSeries.coeff (Finsupp.tail t) ((ω.coeff (t 0)).1) := by have hval …
    rw [hval, MvPowerSeries.funSuccEquivSymm_coeff, PowerSeries.coeff_map]; exact congrArg …
    (coeff_coe ω (t 0))"
  - Discharge: new-tree Iso.lean `coeff_finSuccEquiv_symm` (:64, exact analogue of legacy's
    `funSuccEquivSymm_coeff`) + `map_finSuccEquiv` (:216) + `Polynomial.coeff_coe`.
  - Attacks: [discharge] all three cited names read at their lines this session; [drift]
    the Finsupp.cons/tail bookkeeping is identical (`Finsupp.tail t`, `t 0`); [edge
    t = 0] both sides = constant coefficient of ω.coeff 0 ✓; [seam] cross-file coeff
    equations must be consumed as terms (legacy convention documented at :171–186 of the
    header; the new tree has no diamond, so `rw` should work — if not, term-mode fallback).
  - SURVIVED. LOC legacy 18 → ~15. Prior-B2 clean.

- **D8** (leaf): `isDistinguishedX0_toMvRestrictedX0_of_monic` — Distinguished.lean:135
  - Source: WPPrep_MV.lean:1301–1310; Quote: > "distinguishedMvGen n c (toMvRestrictedX0
    n c ω) s := (distinguishedMvGen_finSuccEquiv_symm …).mpr (distinguished_of_monic_gen ω
    s ωm ωd (by rw [← Polynomial.norm_toMvRestrictedX0]; exact ωn))"
  - Discharge: D1 + D5 + 1-var `isDistinguished_toRestricted_of_monic` (proven, used by
    tranche-2 prep-polynomial bodies).
  - Attacks: [discharge] 1-var name verified in use this session (T032/T038 bodies);
    [composition] D1∘D5∘1-var — 3 lemmas ≤ 3 ✓; [hypothesis] all three hypotheses (Monic,
    degree, norm) needed — dropping norm breaks distinguishedness at radii ≠ 1 (Gauss term
    of lower monomials can dominate). SURVIVED. LOC ~6. Prior-B2 clean.

## File 2: WeierstrassDivision.lean (Mv)

Context: bounds/q_unique over general `R` + `[NormMulClass R]`; hunit-discharge over
`[NormedField K]`.

- **W1** (leaf): `norm_q_le_of_eq_mul_add` — WeierstrassDivision.lean:40
  - Source: WPPrep_MV.lean:654–670 (`mvWeierstrassDivision_bounds_q`)
  - Quote: > "‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by have hg' : distinguishedGen … := hg; have hf' :
    Φ f = Φ g * Φ q + toRestricted (c 0) r … exact weierstrassDivision_bounds_q_gen …
    [pulled back through the isometry]"
  - Match: transport of 1-var `norm_q_le_of_eq_mul_add` (proven, general R := T) along Φ:
    apply Φ to hf (map_add/map_mul + D4), apply the 1-var bound, rewrite norms by
    Iso.lean:250 + D2.
  - Attacks: [instance] T's NormedCommRing/IsUltrametricDist/NormMulClass instances all
    verified to exist this session; [drift] legacy conclusion identical; [seam] the
    RingEquiv-of-mul step is the known MonoidHomClass quirk site — legacy used explicit
    congrArg/`map_mul (Φ)` term steps; plan the same. SURVIVED. LOC legacy ~17 → ~15.
    Prior-B2 clean.

- **W2** (leaf): `norm_r_le_of_eq_mul_add` — WeierstrassDivision.lean:49 — mirror of W1
  against 1-var `norm_r_le_of_eq_mul_add`; Source WPPrep_MV.lean:671–688; same attack
  block as W1 (SURVIVED); conclusion `‖toMvRestrictedX0 c r‖ ≤ ‖f‖` via D5. LOC ~15.
  Prior-B2 clean.

- **W3** (leaf): `weierstrassDivision_q_unique` — WeierstrassDivision.lean:58
  - Source: WPPrep_MV.lean:689–707; Quote: > "q₁ = q₂ := by … apply Φ-injectivity to the
    transported uniqueness weierstrassDivision_q_unique_gen"
  - Match: transport of 1-var `weierstrassDivision_q_unique` (proven, hypothesis-free);
    conclude `Φ q₁ = Φ q₂` then `(finSuccEquiv).injective`.
  - Attacks: [drift] none; [composition] Φ-inj ∘ 1-var-unique — 2 lemmas; [edge] q₁ = q₂ =
    0 trivial ✓. SURVIVED. LOC ~12. Prior-B2 clean.

- **W4** (leaf): `exists_norm_inv_isUnit` — WeierstrassDivision.lean:76
  - Source: WPPrep_MV.lean:579–608 (`exists_norm_inv_unit_tate`)
  - Quote: > "obtain ⟨k, hk⟩ := Restricted.gaussNorm_achieved' (c 0) hc0.le F … obtain
    ⟨t, ht⟩ := MvRestricted.gaussNorm_achieved … ‖F‖ = ‖λ‖·∏cᵢ^tᵢ·(c 0)^k … refine
    ⟨MvRestricted.C (Fin.tail c) (…)⁻¹, ?_, MvRestricted.isUnit_C …⟩"
  - Match: double norm-attainment (1-var `exists_achievesGaussNorm` at `(c 0)` for the
    `X 0`-index, Mv `exists_achievesGaussNorm` (GaussNorm.lean:70) for the coefficient),
    the attained norm is `‖λ‖ · ∏ cᵢ^{tᵢ} · (c 0)^k` = norm of an explicit product of
    units of `K` by `hc`; invert in `K` and take the constant `C` (RingHom, Basic.lean:146;
    `norm_C` GaussNorm.lean:226; unit via `RingHom.isUnit_map`).
  - Attacks: [hypothesis] `NormedField K` suffices (multiplicativity + inverses; no
    completeness — matches legacy context) ✓; [edge `n = 0`] tail is empty, `t = 0`,
    product empty = 1, statement degenerates to the 1-variable `exists_norm_inv_isUnit`
    argument ✓; [discharge] all five cited new-tree names read at their lines this
    session; the `Finset.prod` norm computation uses `map_prod (normHom)` — same call
    compiles in legacy at this pin; [drift] statement identical modulo `T`-spelling.
  - SURVIVED. LOC legacy 30 → ~35. Prior-B2 clean.

## File 3: BaseChange.lean (Mv)

- **B1** (leaf): `isRestricted_mapAlgebra` — BaseChange.lean:46
  - Source: WPPrep_MV.lean (§5 support, `isRestricted_mapAlgebraMv`, used at :942) + the
    proven 1-var `isRestricted_mapAlgebra` (tranche-2 BaseChange, same statement at
    `σ = Unit`).
  - Match: Gauss terms are preserved coefficientwise by `hiso`; restrictedness is a
    tendsto-along-cofinite statement, `Tendsto.congr` from `hf`.
  - Attacks: [drift] 1-var version proven this session — Mv is the same proof with
    `Finsupp`-indexed cofinite filter; [edge f = 0] trivial ✓; [hypothesis] no Fact needed
    (omitted in skeleton — restrictedness is radius-independent of positivity). SURVIVED.
  - LOC ~10. Prior-B2 clean.

- **B2** (leaf): `norm_mapAlgebra` — BaseChange.lean:69
  - Source: WPPrep_MV.lean:949–956; Quote: > "unfold MvPowerSeries.gaussNorm; exact
    iSup_congr fun t => by rw [MvPowerSeries.coeff_map, hiso]"
  - Attacks: [discharge] `iSup_congr` + `coeff_map` mathlib ✓ in use; [drift] identical;
    [edge] `f = 0` ✓. SURVIVED. LOC ~6. Prior-B2 clean.

- **B3** (leaf): `coeff_finSuccEquiv_mapAlgebra` — BaseChange.lean:85
  - Source: WPPrep_MV.lean:969–1007 (private `finSuccEquiv_map` :974–982 + the calc
    :985–1007); Quote: > "Φ_L ∘ mapAlgebra = (coefficientwise mapAlgebra) ∘ Φ_K …
    calc … = PowerSeries.coeff j (PowerSeries.map (MvPowerSeries.map (algebraMap K L))
    (MvPowerSeries.finSuccEquiv K n f.1)) …"
  - Match: raw intertwining `MvPowerSeries.finSuccEquiv L n (map φ F) = PowerSeries.map
    (map φ) (finSuccEquiv K n F)` (ext + coeff_coeff_finSuccEquiv, private helper) + a
    Subtype.ext calc through new-tree `coeff_finSuccEquiv` (Iso.lean:223).
  - Attacks: [seam] the calc is term-mode in legacy precisely because of cross-file coeff
    equations — new tree is diamond-free, but plan term-mode anyway; [discharge]
    `coeff_coeff_finSuccEquiv` is mathlib (`Mathlib.RingTheory.MvPowerSeries.Equiv`,
    imported by Iso.lean) ✓; [drift] none. SURVIVED. LOC legacy ~40 → ~35 (incl. private
    helper). Prior-B2 clean.

- **B4** (leaf): `mapAlgebra_toMvRestrictedX0` — BaseChange.lean:93
  - Source: WPPrep_MV.lean:1009–1020; Quote: > "refine Subtype.ext (MvPowerSeries.ext fun
    t => ?_); rw [mapAlgebra_coe, coeff_map, coeff_toMvRestrictedX0,
    coeff_toMvRestrictedX0, Polynomial.coeff_map, mapAlgebra_coe, coeff_map]"
  - Discharge: D7 twice + coeff_map lemmas. Attacks: [composition] pure coefficient
    computation, both sides `algebraMap` at cons-split exponents; [drift] none; [edge
    ω = 0] ✓ map_zero. SURVIVED. LOC ~10. Prior-B2 clean.

- **B5** (leaf): `isDistinguishedX0_mapAlgebra` — BaseChange.lean:101
  - Source: WPPrep_MV.lean:1022–1035+; Quote: > "obtain ⟨h1, h2, h3⟩ := hf'; refine
    ⟨?_, ?_, ?_⟩; · rw [MvRestricted.coeff_finSuccEquiv_mapAlgebra n c L hiso f s] …"
  - Match: the three fields of `IsDistinguished` (unit coefficient — maps by
    `RingHom.isUnit_map` through B3; Gauss-term equality and strict domination — preserved
    by the isometry B2 applied slice-wise via B3).
  - Attacks: [structure] new-tree `IsDistinguished` is a structure with fields
    isUnit_coeff / gaussNorm_eq / lt_of_gt — legacy `distinguishedGen` had the same three
    (⟨h1, h2, h3⟩ destructuring in the quote); field-by-field transport matches; [seam]
    B3 rewrites at coefficient level — known quirk site, plan term steps; [drift] none.
  - SURVIVED. LOC legacy ~35 → ~30. Prior-B2 clean.

- **B6** (leaf): `weierstrassDivision_descend` — BaseChange.lean:117
  - Source: WPPrep_MV.lean:1150–1246; Quote (head): > "letI : NormedSpace K L := ⟨fun a x
    => le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩; obtain ⟨π, hπcomp⟩ :=
    LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L) …; obtain ⟨Cπ, -,
    hCπ⟩ := SemilinearMapClass.bound_of_continuous π …"
  - Match: the 1-variable `weierstrassDivision_descend` (tranche-2 BaseChange, PROVEN this
    session, ~120 lines) with `Finsupp`-indexed coefficients instead of ℕ-indexed: bounded
    retraction π from finite-dimensionality; apply π to every multivariate coefficient of
    q and r; the retracted data divides f (the `lmap_mul` antidiagonal computation is the
    `Finsupp.antidiagonal` clone); the difference is an L-division of 0 killed by W1/W2
    over L.
  - Attacks: [source-strength] BOTH sources compile — legacy Mv at this pin AND the 1-var
    port proven sorry-free this session; the only delta is ℕ → `Fin (n+1) →₀ ℕ`
    bookkeeping; [discharge] `LinearMap.exists_leftInverse_of_injective` +
    `SemilinearMapClass.bound_of_continuous` + `continuous_of_finiteDimensional` all used
    by the 1-var port at this pin (imports already in the skeleton); [known trap]
    `letI` (not `have`) for NormedSpace — documented tranche-2 landmine, carried into the
    plan; [known trap] `map_mul`/`linear_combination` MonoidHomClass quirk at the hzero
    step — 1-var solved with explicit `RingHom.map_mul` term; same plan. SURVIVED.
  - LOC legacy 96 → ~110. Prior-B2 clean.

## File 4: DivisibleRadius.lean (Mv)

- **E1** (leaf, private): `extension_frame` — DivisibleRadius.lean:41
  - Source: WPPrep_MV.lean:1313–1358; Quote: > "choose m hm x hx using hdiv; choose α hα
    using fun i => IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (x i))
    (Nat.pos_of_ne_zero (hm i)); … IntermediateField.adjoin K (Set.range α) …
    haveI : Finite (Set.range α) := (Set.finite_range α).to_subtype; haveI hfin :
    FiniteDimensional K … := IntermediateField.finiteDimensional_adjoin …
    letI : NontriviallyNormedField … := spectralNorm.nontriviallyNormedField K _ …"
  - Match: identical construction; the instance block is the T030 block (proven 1-var this
    session at this pin) with `adjoin (Set.range α)` for `K⟮α⟯` and
    `finiteDimensional_adjoin` for `adjoin.finiteDimensional`.
  - Attacks: [discharge] every cited name compiles in BOTH the legacy at this pin and
    (modulo the single-root vs range-of-roots delta) the 1-var T030 port; the two deltas
    (`Set.finite_range`, `IntermediateField.finiteDimensional_adjoin`) compile in legacy at
    this pin — verified by the 2614-job build; [universe] eliminator quantifies
    `L : Type u` with `K : Type u` — legacy identical, skeleton elaborates ✓; [edge] all
    radii already unit norms: frame still sound (adjoin of roots of units) ✓. SURVIVED.
  - LOC legacy 46 → ~55. Prior-B2 clean.

- **E2** (leaf, private): `weierstrassDivision_exists_of_forall_units` —
  DivisibleRadius.lean:50
  - Source: WPPrep_MV.lean:708–725 (`mvWeierstrassDivision_existance`)
  - Quote: > "obtain ⟨q', r', hr', hf'⟩ := weierstrassDivision_existance_gen … (Φ g) s hg
    (Φ f) [hunit := exists_norm_inv_unit_tate hc] …; exact ⟨Φ.symm q', r', hr', [pull-back
    calc]⟩"
  - Match: 1-var `weierstrassDivision_exists` (proven, general R := T, hunit := W4) on
    `Φ g, Φ f`; pull back with Φ.symm + D4; degree untouched.
  - Attacks: [instance] the 1-var exists needs NormOneClass T + NeBot T — both instances
    exist (GaussNorm.lean:237/:268 with NeBot K from `NormedField.nhdsNE_neBot`, the same
    local-instance trick as 1-var T030) ✓; [drift] none; [composition] Φ ring-iso steps at
    the known quirk sites — term-mode plan. SURVIVED. LOC legacy 18 → ~20. Prior-B2 clean.

- **E3** (leaf): `weierstrassDivision_exists_divisible` — DivisibleRadius.lean:61
  - Source: WPPrep_MV.lean:1360–1374; Quote: > "refine extension_frame n c hdiv ?_; intro
    L _ _ _ _ _ hiso hcL; obtain ⟨qL, rL, hrL, hfL⟩ := mvWeierstrassDivision_existance n c
    hcL (mapAlgebra L c hiso g) s (distinguishedMvGen_mapAlgebra …) (mapAlgebra L c hiso
    f); obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ := mvWeierstrassDivision_descend …; exact ⟨q₀, r₀,
    hr₀, heq⟩"
  - Discharge: E1 + E2(over L) + B5 + B6 — the exact legacy composition.
  - Attacks: [composition] four proven-or-planned leaves in the legacy's own order —
    machine-validated composition; [hypothesis] `hdiv` per-coordinate is exactly what E1
    consumes; [drift] none. SURVIVED. LOC legacy 15 → ~15. Prior-B2 clean.

- **E4** (leaf): `weierstrassDivision_uniqueness_divisible` — DivisibleRadius.lean:69
  - Source: WPPrep_MV.lean:1377–1391 + the tranche-2 1-var mirror (uniqueness = exists +
    `toMvRestrictedX0_injective` remainder-cancellation + W3).
  - Quote: > "refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩ · rintro r' ⟨hr', hf'⟩; exact
    [injective] (add_left_cancel (hf'.symm.trans hf₀)) · rintro q' …; exact
    [q_unique] …" (the shipped 1-var shape, proven 3× this session)
  - Attacks: [composition] E3 + D6 + W3, ≤ 3 ✓; [drift] none; [edge] uniqueness at f = 0 ✓.
  - SURVIVED. LOC ~8. Prior-B2 clean.

- **E5** (leaf): `weierstrassDivision_polynomial_divisible` — DivisibleRadius.lean:78
  - Source: WPPrep_MV.lean:1393–1469; and the twice-proven tranche-2 1-var body (monic
    rescale `C ↑u⁻¹ * g₀`, `modByMonic_add_div`, `degree_modByMonic_lt`, `key` argument).
  - Quote: > "have hgu : IsUnit (g₀.coeff s) … obtain ⟨u, hu⟩ := hgu … Polynomial.C
    (↑u⁻¹ …) * g₀ … modByMonic_add_div … key : ∀ q' r', … → q' = Q"
  - Match: the coefficient ring is now `T` (comm ring, not a field) — the body never
    inverts non-units: it needs exactly `IsUnit (g₀.coeff s)`, which distinguishedness
    provides (via D1 + `Polynomial.coeff_coe` at the `T`-level). `hgs` KEPT (necessary).
  - Attacks: [hypothesis] over a RING the monic-rescale argument requires the coeff-s unit
    — present; polynomial division by a monic works over any comm ring
    (`modByMonic_add_div`) ✓; [drift] legacy proved the same statement over T at :1393;
    [prior-B2 shape-check] the tranche-2 finding (spurious `hgs` on PREP-polynomial only)
    re-checked: division-polynomial DOES need `hgs` — 1-var counterexample transports
    (`g₀ = X0^s + p•X0^(s+1)` over `ℤ_p⟮tail⟯`). SURVIVED. LOC legacy 77 → ~55. Prior-B2
    clean.

- **E6** (leaf): `weierstrassDivision_exists_of_not_memDivisibleValueGroup` —
  DivisibleRadius.lean:95 — **NEW MATHEMATICS**
  - Prose proof (Step 1, tranche-2 precedent): Let `T := Restricted K (Fin.tail c)` and
    `G := finSuccEquiv g`, so `hg` says `G.1` is `IsDistinguished` over `T` at `(c 0)` of
    degree `s` — definitionally (D1/def). Since `¬MemDivisibleValueGroup T (c 0)`, the
    1-variable no-tie lemma `forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup`
    (proven this session, stated over ANY `[NormedCommRing R'] [IsUltrametricDist R']
    [NormMulClass R']` — instantiate `R' := T`) yields strict domination of every Gauss
    term of `G` by the `s`-th. The strictly-dominated capstone
    `weierstrassDivision_exists_of_forall_lt` (proven this session, general `R'` +
    `[CompleteSpace R']` — instance for `T` at Complete.lean:89) divides `F := finSuccEquiv
    f`: `F = G * Q + toRestricted (c 0) R₀`, `deg R₀ < s`. Pull back through `Φ.symm`
    (ring isomorphism + D4): `f = g * Φ.symm Q + toMvRestrictedX0 R₀`. ∎
  - Source quotes (the two engines, project code read this session): 1-var
    DivisibleRadius.lean `lemma forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup
    (hc : ¬MemDivisibleValueGroup R c) … : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s
    g.1‖ * c ^ s`; 1-var WeierstrassDivision.lean `theorem
    weierstrassDivision_exists_of_forall_lt [CompleteSpace R] … (hstrict : ∀ t, t ≠ s →
    …) (f) : ∃ q r, r.degree < s ∧ f = g * q + Polynomial.toRestricted c r`.
  - Attacks: [instance audit] T needs NormedCommRing ✓, IsUltrametricDist ✓, NormMulClass ✓
    (requires `NormMulClass K` — holds, K is a normed field), CompleteSpace ✓ (general-σ
    instance) — all four read at their lines this session; [hypothesis-strength] NO
    condition on tail radii is needed — the tail radii enter only through T's norm, and
    `MemDivisibleValueGroup T (c 0)` is exactly the tie obstruction (a tie would produce
    `(c 0)^(s-t) = ‖aₜ·u⁻¹‖` with `aₜ·u⁻¹ ∈ T` — the no-tie proof is verbatim the 1-var
    one at base T); CANNOT be weakened to `¬MemDivisibleValueGroup K (c 0)` — over
    `c = (r, r)` with `r` irrational, `X 1 ∈ T` realises `c 0`, ties occur, engine
    genuinely fails: the hypothesis is sharp; [transport] pull-back skeleton is E2's
    (machine-validated shape). SURVIVED. LOC ~18 (no legacy; grounded on E2's 18 + no-tie
    application 2 lines). Prior-B2 clean.

- **E7** (leaf): `weierstrassDivision_uniqueness_of_not_memDivisibleValueGroup` —
  DivisibleRadius.lean:104 — mirror of E4 with E6 as the exists. Attacks: as E4
  (composition E6 + D6 + W3). SURVIVED. LOC ~8. Prior-B2 clean.

- **E8** (leaf): `weierstrassDivision_polynomial_of_not_memDivisibleValueGroup` —
  DivisibleRadius.lean:112 — mirror of E5 with E7 as the uniqueness. Attacks: as E5.
  SURVIVED. LOC ~55. Prior-B2 clean.

- **E9** (leaf): `weierstrassPreparation_exists_divisible` — DivisibleRadius.lean:131
  - Match: the 1-variable trick `weierstrassPreparation_exists_of_forall_exists` (proven,
    general `R' := T`) over `(T, c 0)` with oracle = E3 transported to the Φ-side (for
    `g' s' hg' f'`: apply E3 to `Φ.symm`-pullbacks, push the witness forward — or
    equivalently run the trick on `Φ g` and pull the ω/e pair back through
    D1/D4/D5/`isUnit_finSuccEquiv_symm_iff`). The unit is built at `K`-level by
    q-uniqueness — no descent of units.
  - Source quote (trick, project code): 1-var WeierstrassPrep.lean:86 `theorem
    weierstrassPreparation_exists_of_forall_exists … (hdiv : ∀ g s, IsDistinguished … → ∀
    f, ∃ q r, …) … : ∃ ω e, ω.Monic ∧ ω.degree = s ∧ ‖…‖ = c ^ s ∧ IsUnit e ∧ g = e * …`.
  - Attacks: [oracle-shape] the trick's oracle quantifies over ALL distinguished g' at
    `(T, c 0)` — E3's Mv statement supplies it for pullbacks of such g' since
    `IsDistinguishedX0 (Φ.symm g') ↔ IsDistinguished g'` (D1) and every `Restricted T
    (c 0)`-series IS a pullback (Φ surjective): no generality gap; [deviation-from-legacy
    justified] legacy §5-prep (1471–1600) descended units instead — the trick supersedes
    (twice-validated in tranche 2); [norm] `‖toMvRestrictedX0 ω‖ = (c 0)^s` via D5.
    SURVIVED. LOC ~20. Prior-B2 clean.

- **E10** (leaf): `weierstrassPreparation_unique_divisible` — DivisibleRadius.lean:139 —
  mirror of the tranche-2 1-var prep-unique body at Mv (E9 exists; e-uniqueness by
  norm-cancellation `‖toMvRestrictedX0 ω‖ = (c 0)^s ≠ 0` + NormMulClass T-side; ω-uniqueness
  by `degree_sub_lt` + W2 at `f := 0` + D6). Source: WPPrep_MV.lean:1556–1600 + the
  twice-proven 1-var body. Attacks: [composition] all five ingredients exist at Mv (E9,
  D5, D6, W2, Polynomial.degree_sub_lt) ✓; [edge] two preparations of the same g ✓ handled
  exactly as 1-var; [drift] legacy statement identical. SURVIVED. LOC ~40. Prior-B2 clean.

- **E11** (leaf): `weierstrassPreparation_polynomial_divisible` — DivisibleRadius.lean:149
  — mirror of the tranche-2 1-var prep-polynomial body (E10 + E5 + W3 + D8; NO `hgs` —
  matches legacy :1602 and the tranche-2 finding). Attacks: [hypothesis] `hgs`-free
  verified against legacy quote above; [composition] ≤ 4 project lemmas, the 1-var body
  compiled twice this session; [unit-ness caveat] `IsUnit (toMvRestrictedX0 e)` not
  `IsUnit e` in `T[X]` — documented, matches 1-var docstring caveat. SURVIVED. LOC ~45.
  Prior-B2 clean.

- **E12–E14** (leaves): prep trio `_of_not_memDivisibleValueGroup` —
  DivisibleRadius.lean:160/168/177 — E9/E10/E11 with E6-oracle instead of E3. Attacks:
  identical blocks; the trick and mirrors are régime-agnostic given the division oracle
  (the entire point of the tranche-2 architecture). SURVIVED. LOC ~20/40/45. Prior-B2
  clean.

## Prior-B2 log consultation (Step 4.6)

`.mathlib-quality/b2_log.jsonl`: file was absent; created empty this session. 0 entries —
every leaf trivially clean by name and by shape. The one historical statement-defect
pattern (spurious `hgs` on prep-polynomial, tranche-2 in-session finding, never a formal
B2) was re-applied as an edge-check on E5/E8 (kept — necessary for DIVISION-polynomial)
and E11/E14 (dropped — absent in legacy too).

## Confidence gate (Step 5)

1. Every leaf discharges from mathlib (verified in use at this pin), from proven new-tree
   project code (read at file:line this session), or from the legacy composition whose
   every analytic input is re-pointed at proven code. No REVIEW-PENDING leaves. ✓
2. Skeleton compiles: 2637 jobs, sorries only (32), no type errors. ✓
3. Every leaf has a verbatim source quote (legacy Lean at exact lines / project tranche-2
   decls / prose for E6 per the tranche-2 in-session-prose precedent) + a match paragraph. ✓
4. Every leaf and both nontrivial compositions (E3's frame-descend chain; E9's
   trick-oracle) carry attack blocks with ≥ 3 executed attacks; the source-trust attack
   FOUND a real flaw (legacy sorryAx) and the tree REPAIRS it (remap table). ✓
5. B2 log consulted (0 entries). ✓
6. Tree mirrors the source's own structure (§0→Distinguished, §2→dictionary,
   §3→W4, §4→W1–W3/E2, §5→B*/E1/E3–E5) with each deviation from the source listed and
   justified (7 items); LOC estimates grounded in legacy line counts throughout. ✓
7. Single-conclusion check: every leaf is one declaration with one conclusion; the ∃!-
   nestings are single statements (shared-witness existentials, the documented exception);
   descend's 4-part conclusion is a shared-witness existential over (q₀, r₀) (same shape
   as the proven 1-var descend — kept per statement-splitting exception, one-line
   justification: the witnesses are shared and consumed together by E3). ✓

**GATE PASSES.**

---

# Tranche 3b amendment (2026-07-25): every-polyradius Mv Weierstrass via Gauss extensions

## Scope escalation (user-pinned)

"Having Mv WP with general c is the ultimate goal." The Gauss-point route (option 1 of the
alternatives analysis) is now IN scope. Consequences applied immediately, before any
endpoint was proven:

* The six `_of_not_memDivisibleValueGroup` endpoints of the tranche-3 tree (E6–E8,
  E12–E14) are **DELETED from the skeleton** — the unconditional theorems subsume them
  (a head radius outside the divisible closure is handled by adjoining its Gauss
  extension), so building them would repeat the redundancy pruned from the 1-variable
  layer. Their attack blocks above remain as the record of why the hypothesis was sharp.
* `weierstrassDivision_exists_divisible` (E3) and the prep/uniqueness/polynomial mirrors
  lose their public status: E3 becomes the PRIVATE base case of a radius-count induction;
  the mirrors (former E4/E5/E9–E11 bodies) attach to the new **unconditional public six**
  `MvPowerSeries.Restricted.weierstrassDivision_{exists,uniqueness,polynomial}` and
  `weierstrassPreparation_{exists,unique,polynomial}` — no radius hypotheses.

## Already implemented this session (proven, green)

**The descend refactor** (flagged twice in earlier analyses as the prerequisite):
`PowerSeries.Restricted.weierstrassDivision_descend_of_retraction` — the 1-variable
descent now takes the bounded retraction as data `(π : L →ₗ[K] K) (hπ) {Cπ} (hCπ)`; the
former `[Module.Finite K L]` theorem is a 6-line corollary manufacturing `π` from
finite-dimensionality (the exact code block that previously opened the proof). Body reused
verbatim; the 1-variable tree rebuilt green (2570 jobs, still sorry-free). The Mv skeleton
carries the same split (`weierstrassDivision_descend_of_retraction` sorried core + finite
corollary whose 6-line proof already compiles against it).

## New skeleton files (build green, 2642 jobs)

- `PhD/ForMathlib/RingTheory/LaurentPolynomial/GaussNorm.lean` — Gauss norm on Laurent
  polynomials + the `GaussLaurent K r` normed type synonym (24 sorry sites).
- `PhD/ForMathlib/RingTheory/LaurentPolynomial/GaussExtension.lean` — the completed
  Gauss-point field + retraction (15 sorry sites).
- Mv `BaseChange.lean` gains the retraction-form descend; Mv `DivisibleRadius.lean`
  restructured (10 sorry sites: frame, hc-rung, divisible base case, card-induction,
  unconditional six).

## Source situation for the new layer

No legacy Lean and no on-disk text covers the Gauss extension; the construction is
standard (the completed residue field `H(η_r)` of the Gauss point — Berkovich-style;
BGR-adjacent). Per the tranche-2 precedent for new mathematics, each leaf below carries an
in-session prose proof; the adversarial pass substitutes for source quotes, and the two
external-facing claims (annulus algebra is a field off the divisible closure; Gauss norm
multiplicative there) are *derived in prose from first principles below*, not cited.

## New leaves (grouped; per-group prose, discharge, attacks)

### G-A: `LaurentPolynomial.gaussNorm` basics (9 leaves, GaussNorm.lean:36–75)

Prose: `gaussNorm r p = ⨆ m : ℤ, ‖p.coeff m‖ * r^m`; the family is 0 off the finite
support, so the iSup is a finite max ∪ {0}: nonneg, attained when `p ≠ 0`, `le_gaussNorm`
by `le_ciSup` (BddAbove from finiteness), `gaussNorm_zero` collapses to `⨆ _, 0 = 0`,
eq-zero-iff from attainment + `r^m > 0` (zpow of a positive real), `C`/`T` values by
support-singleton collapse, ultrametric add ≤ max and submultiplicativity coefficientwise
(`coeff (p*q) m` is a finite antidiagonal sum; ultrametric max-bound + term bound
`‖p_i‖r^i · ‖q_j‖r^j ≤ ‖p‖‖q‖`).
- Discharge: mirrors of the project's Mv `GaussNorm.lean` proofs at finite support (read
  this session); mathlib `zpow_pos`, `Real.iSup_*`, `le_ciSup`, ultrametric
  `norm_sum_le_of_forall` family (in use in the Mv file).
- Attacks: [edge `p = 0`] handled by dedicated lemma, iSup of the zero family ✓; [zpow]
  exponents are `ℤ` — all positivity/monotonicity cited as `zpow` versions, recorded so
  the worker doesn't reach for `pow` lemmas; [API-existence] statements deliberately use
  only `p.coeff` (verified present: `LaurentPolynomial.ext`, `C_apply`, `T_apply` read at
  this pin) — `AddMonoidAlgebra` is a *structure* here, so support-based drafts were
  rejected at design time; the attained-norm leaf may need a support access
  (`p.toFinsupp.support`-analogue) — flagged as the one API-risk in the group, with the
  fallback of stating via `Function.support` finiteness. SURVIVED. LOC ~120 total,
  grounded on the Mv analogues (each ≤ 15 lines there).

### G-B: no-tie and multiplicativity (2 leaves, GaussNorm.lean:79–95)

Prose (tie): `‖a‖ r^i = ‖b‖ r^j`, `i ≠ j`, `a, b ≠ 0` over the field `K`. If `i > j`:
`r^(i-j) = ‖b‖/‖a‖ = ‖b * a⁻¹‖` with `i - j > 0`, exhibiting
`MemDivisibleValueGroup K r` (witness `n := (i-j).toNat ≠ 0`); if `i < j` symmetrically
with `a * b⁻¹`. Contradiction.
Prose (multiplicativity): both factors have unique dominant exponents `i₀, j₀` (ties
impossible by the previous leaf); in `coeff (p*q) (i₀+j₀)` the term `p_{i₀} q_{j₀}`
strictly dominates every other antidiagonal term (each other term has a strictly smaller
Gauss-term product), so ultrametric addition gives
`‖coeff (p*q) (i₀+j₀)‖ r^(i₀+j₀) = ‖p‖‖q‖`; combined with submultiplicativity, equality.
- Discharge: `norm_mul` on `K` (NormedField), `IsUltrametricDist.norm_add_le_max`-family,
  the G-A attained lemma.
- Attacks: [sign] the ℤ-exponent sign split is explicit in the prose (the 1-variable
  no-tie only faced `t < s` — the Laurent version faces both; recorded so the worker
  writes both branches); [hypothesis] `NormedField K` (inverses) genuinely needed — over a
  ring the tie argument fails, matching the type-synonym design that fixes `K` a field for
  the `NormMulClass` instance; [edge] `p` or `q` a monomial: dominant term is the only
  term ✓. SURVIVED. LOC ~60, grounded on the 1-variable no-tie (~25 proven lines) + the
  dominant-product legacy shape.

### G-C: `GaussLaurent` instance pack (8 leaves, GaussNorm.lean:100–175)

`gaussRingNorm` fields = G-A leaves; `RingNorm.toNormedRing` is the exact instance path
the Mv tree already uses (GaussNorm.lean:173, read this session), so the metric/uniformity
is canonical; `IsUltrametricDist` from add ≤ max; `norm_C`/`norm_T` from G-A; `coeffZero`
linear (coefficientwise), `‖coeffZero p‖ ≤ ‖p‖` since `‖p.coeff 0‖ * r^0` is one term of
the sup; `NormMulClass` [Fact ¬MemDVG] from G-B.
- Attacks: [instance-path] `RingNorm.toNormedRing` chosen deliberately so `Completion`
  sees the canonical uniformity — same-pattern precedent in-tree; [smul] `map_smul'` of
  `coeffZero` is coefficientwise `Algebra.id`-smul — the `Algebra K (GaussLaurent K r)`
  instance is `C.toAlgebra`, so `smul = C a * p` needs the `coeff_C_mul`-style Laurent
  lemma (exists in mathlib Laurent API as multiplication by `C`; flagged);
  [Fact-plumbing] `Fact (¬MemDivisibleValueGroup K r)` mirrors the tree's `Fact (0 < c)`
  convention. SURVIVED. LOC ~100.

### G-D: `GaussExtension` completion pack (10 leaves, GaussExtension.lean:40–80)

Prose: `GaussExtension K r := UniformSpace.Completion (GaussLaurent K r)`. Ring structure:
mathlib `Topology/Algebra/UniformRing` (✓ read: exists). Norm layer: mathlib has the
NormedAddCommGroup completion (`Completion.norm_coe` read at this pin) but **no
`NormedRing (Completion A)` instance — a genuine mathlib gap**; the leaf assembles it
(norm_mul_le extends from the dense subring by continuity of `‖·‖` and `*`) and is
PR-able upstream. `IsUltrametricDist`: closed condition, density. `ofLaurent` =
`Completion.coeRingHom`; isometry = `norm_coe`; `DenseRange` = `Completion.denseRange_coe`.
`exists_unit_norm`: the image of the Laurent unit `T` (units map to units along ring homs)
with `‖T‖ = r`. `memDivisibleValueGroup_self`: witness `n = 1`. `_of_base`: push the
`K`-witness through the isometric `algebraMap`.
- Attacks: [INSTANCE DIAMOND — real defect found at design time] the skeleton currently
  declares `NormedCommRing` (Fact-free) and `NontriviallyNormedField` (under Facts) as
  independent sorried instances: under Fact contexts two norm paths exist. BINDING
  assembly note: the field instance must be built SHARING the ring/norm data
  (`__ := inferInstanceAs (NormedCommRing _)`, `Field` via `IsField.toField` on the SAME
  `CommRing`), eliminating the diamond; the worker must not prove the two independently.
  [mathlib-gap honesty] the NormedRing-on-completion leaf is flagged as new
  general-purpose infrastructure (small, ~40 lines) rather than silently assumed.
  SURVIVED with the recorded design obligation. LOC ~150.

### G-E: the retraction (3 leaves, GaussExtension.lean:84–99)

Prose: `coeffZero : GaussLaurent K r →ₗ[K] K` is bounded (norm ≤ 1 constant), hence
uniformly continuous; `K` is complete; `Completion.extension` gives
`retraction : GaussExtension K r → K`, linear by density (both sides of additivity/smul
are continuous and agree on the dense range), `retraction ∘ algebraMap = id` since on
constants `coeffZero (C a) = a` (`Completion.extension_coe`), and `‖retraction x‖ ≤ ‖x‖`
extends the Laurent bound by density.
- Discharge: `UniformSpace.Completion.extension`, `extension_coe`,
  `Completion.induction_on` (all standard, in mathlib at this pin), G-C's `coeffZero`
  lemmas.
- Attacks: [continuity prerequisite] `extension_coe` requires uniform continuity of the
  seed — supplied by the explicit bound (`LipschitzWith.uniformContinuous`); [linearity]
  not free from `extension` — proven by density, recorded as an explicit step, not
  assumed; [norm-1] `Cπ = 1` feeds `weierstrassDivision_descend_of_retraction` directly.
  SURVIVED. LOC ~70.

### G-F: the field instance (2 leaves, GaussExtension.lean:103–117)

Prose (IsField): `x ≠ 0` in the completion; pick Laurent `p` with `‖x - p‖ < ‖x‖`
(density), so `‖p‖ = ‖x‖ ≠ 0` (ultrametric isoceles); `p` has a unique dominant monomial
`a·T^m` (G-B no-tie), which is a unit (`a ∈ Kˣ`, `T^m` a unit); `‖p - a·T^m‖ < ‖p‖`, so
`x = (a·T^m)·(1 + u)` with `‖u‖ < 1` — hmm, assembled as: `x = p + (x - p)` with both
error terms `< ‖x‖`, so `x = a·T^m·(1 + w)`, `‖w‖ < 1`, and `1 + w` is a unit by geometric
series in the complete ring. Hence every nonzero is a unit: `IsField`, then
`IsField.toField` (noncomputable), then `NontriviallyNormedField` by data-sharing assembly
(G-D note) with the nontriviality witness from `K`. `NormMulClass`: extends G-B/G-C
multiplicativity from the dense subring by continuity.
- Attacks: [where each hypothesis lands] completeness → geometric series; ¬MemDVG →
  unique dominant monomial; density → approximation: all three load-bearing, none
  droppable — matches the classical statement that the annulus algebra is a field
  *exactly* off the divisible closure (for `r` in the closure it has zero divisors — no:
  it is a domain but non-field, e.g. `t - a` at `|a| = r` is a non-unit; recorded as the
  reason the Fact is not removable); [geometric series] mathlib
  `Units.oneSub`/`NormedRing.inverse`-style one-minus-small units:
  `Units.oneSub (h : ‖t‖ < 1)` exists for complete normed rings (used in-tree via
  `IsTopologicallyNilpotent`-adjacent lemmas; fallback `tsum` construction). SURVIVED.
  LOC ~90.

### G-G: Mv descend, retraction form (1 leaf, Mv BaseChange.lean:117)

Unchanged content from the tranche-3 B6 entry (all attacks carry over); the signature now
takes `(π, hπ, hCπ)` and the finite corollary's 6-line proof is already REAL in the
skeleton (compiles against the sorried core — the dependency shape is machine-checked).

### G-H: the radius-count induction (1 leaf, Mv DivisibleRadius.lean:78)

Prose: induction on `N` for the statement "for every complete nontrivially normed
ultrametric `K : Type u` and radius tuple with `Nat.card {i // ¬MemDivisibleValueGroup K
(c i)} ≤ N`, division holds". `N = 0`: every radius divisible — the private base case
(finite spectral frame + hc-rung + finite descend; the machine-checked legacy composition,
entries E1–E3 above). Step: if all radii divisible, base case; else pick `i₀` with
`¬MemDivisibleValueGroup K (c i₀)`, set `L := GaussExtension K (c i₀)` with the two Facts;
`L` is complete nontrivially normed ultrametric (G-D/G-F) in the SAME universe (Completion
of an `AddMonoidAlgebra` structure stays in `Type u`); the unrealised set over `L` injects
into (unrealised over `K`) \ {i₀} (`memDivisibleValueGroup_of_base` + `_self`), so its
`Nat.card` drops by ≥ 1 — apply the inductive hypothesis over `L` to the base-changed data
(`mapAlgebra`, `isDistinguishedX0_mapAlgebra`), then descend along the Gauss retraction
(`weierstrassDivision_descend_of_retraction` + G-E, `Cπ = 1`).
- Attacks: [universe] the ∀-over-`K` quantification at fixed `Type u` mirrors the proven
  legacy `extension_frame` eliminator pattern; `GaussExtension` verified to stay in
  `Type u` by the skeleton's elaboration; [cardinal bookkeeping] `Nat.card` on subtypes of
  `Fin (n+1)` — finite, `Nat.card_le_card_of_injective` on the inclusion (mathlib);
  chosen over `Finset.filter` precisely to avoid `DecidablePred` plumbing (design attack
  executed: the filter draft was rejected); [termination] count strictly drops since `i₀`
  leaves the set and no index enters it (monotonicity) — the two memDVG lemmas are exactly
  what is needed, no more; [Fact plumbing] `Fact (0 < c i₀)` from the tuple Fact,
  `Fact (¬MemDVG K (c i₀))` by `Fact.mk` on the case hypothesis. SURVIVED. LOC ~60.

### G-I: the public six (6 leaves, Mv DivisibleRadius.lean:95–160)

`weierstrassDivision_exists` = G-H at `N := Nat.card _` (`le_refl`). Uniqueness /
polynomial / prep exists / prep unique / prep polynomial: the standard mirrors — identical
to the former E4/E5/E9/E10/E11 bodies (attacks and sources recorded there) with the
`hdiv` hypothesis deleted and the unconditional exists as the oracle. All five bodies were
proven twice at the 1-variable layer this session; `hgs` kept on division-polynomial,
absent on prep-polynomial (E5/E11 audit carries over).

## Prior-B2 log: still 0 entries; all new leaves clean by name and shape.

## Confidence gate (re-run for the amended tree)

1. Every leaf discharges from mathlib (verified in use), proven project code, the
   machine-checked legacy composition, or carries a first-principles prose proof with an
   executed attack block (G-A…G-I). One declared mathlib gap (NormedRing on Completion) is
   scoped as a small self-contained leaf, not hidden. ✓
2. Skeleton compiles: 2642 jobs, sorries only; the 1-variable tree REMAINS sorry-free
   after the descend refactor (2570 jobs). ✓
3. Quotes/matches: legacy-backed leaves cite exact lines; new-mathematics leaves carry
   prose per the tranche-2 precedent. ✓
4. Adversarial pass: executed per group; two REAL defects found and recorded as binding
   obligations (instance-diamond assembly note in G-D; sign-split in G-B). ✓
5. B2 log consulted (empty). ✓
6. Tree mirrors its sources (legacy composition + the twice-proven 1-variable bodies);
   LOC grounded throughout; deviations listed with justifications. ✓
7. Single-conclusion check: unchanged from tranche 3 (shared-witness existentials
   documented). ✓

**GATE PASSES** (amended tree). Ticket creation still pending user approval.
