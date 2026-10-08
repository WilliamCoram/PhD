# Ticket board: Tau Ceti `RigidAnalyticGeometry`, Layer 0 (the Tate algebras)

**Board**: `.mathlib-quality/tauceti-rag-layer0/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 (§0.1–§0.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/RigidAnalyticGeometry/` (and `PadicFunctionalAnalysis/Orthonormal.lean`) — 19 files,
every declaration already stated with `sorry`; the floor `Restricted/**` and `TateAlgebra/Tower.lean` are
complete. Planned 2026-10-02. Status: **COMPLETE — `/beastmode` 2026-10-02/05: all 117 tickets done; sorry-free, standard axioms, `lake build PhD.TauCeti` passes, `runLinter` clean on every module.**

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 81 (`T001`–`T081`; `T081` is the chain-root gate) |
| Per-file cleanups | 31 (`CLEANUP-1`–`CLEANUP-31`) |
| Pre-milestone sweeps | 4 (`CLEANUP-ALL-1`–`CLEANUP-ALL-4`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **117** |

- **Milestone M1** = `T028`: the Gauss norm of `Tₙ` is the supremum norm
  (`MvPowerSeries.Restricted.supSeminorm_eq_norm`) — [RM] §0.1.3–§0.1.4, BGR 5.1.4/6.
- **Milestone M2** = `T050`: `Tₙ` is noetherian, factorial, Jacobson and of Krull dimension `n` — [RM]
  §0.3.2–§0.3.4, BGR 5.2.6/1–3.
- **Milestone M3** = `T070`: ideals of `Tₙ` are strictly closed and `|Tₙ ⧸ 𝔞| = |K|` — [RM] §0.3.1,
  BGR 5.2.7/8, Bosch 1.3/7–9.
- **Milestone M4** = `T077`: `Q(Tₙ)` is weakly stable and `Tₙ` is Japanese, in characteristic zero —
  [RM] §0.4.2–§0.4.3, BGR 5.3.1/1 and 5.3.1/3.
- Skeleton: 205 open declarations, 215 `sorry`s. Gate (verified 2026-10-02, 2 722 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T022`, `T025`, `T038`, `T044`,
  `T051`, `T055`, `T062`, `T071`, `T076`.
- **Not on this board**: [RM] §0.4.2–§0.4.3 in characteristic `p` (BGR 5.3.1/2 and Part A's b-separable
  modules). See `plan.md`, "Not on this board", and `decomposition.md`, "Unticketed sub-tree".

## Worker protocol (binding)

1. **The statements are fixed.** Every Statement block is copied verbatim from the skeleton by
   `scratch/gen_tickets.py`. Prove the statement as written. If a statement is false or unprovable as stated,
   that is a **B2 stop** with a concrete counterexample or obstruction — never silently change a hypothesis.
   Private helper lemmas are allowed and expected where a sketch says so.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. The floor
   `Restricted/**` was copied from `PhD/Main/ForMathlib`; do not re-copy or edit it except in `CLEANUP-FINAL`.
   Never delete `PhD/PR'd/` or legacy files.
3. **Seam rules** (plan, "The floor"): `Restricted R c` is opaque — cross it with `Restricted.ext`, `val_*`,
   `congrArg`; no file other than `TateAlgebra/Tower.lean` mentions `Fin.tail`, the floor's `finSuccEquiv` or
   `PowerSeries.Restricted` (use `coeffX0`, `coeff_coeffX0`, `ofPolynomial`, `coeff_ofPolynomial`,
   `isMulDistinguishedX0_iff` and the six Weierstrass statements of `Tower.lean`); if a floor lemma must be
   applied at the unit polyradius, give the polyradius explicitly (`(c := (1 : Fin (n + 1) → ℝ))`).
4. **Never `import Mathlib`** in a file that imports the floor (the floor's `PowerSeries.IsRestricted` clashes
   with `Mathlib.RingTheory.PowerSeries.Restricted`), and do not import that Mathlib file or
   `Mathlib.RingTheory.Polynomial.GaussNorm`. Imports stay minimal per file; when a proof needs an unimported
   module, add exactly that module.
5. **Build** with `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` (or
   `PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal`) — never `lake build PhD`. There is no `timeout`
   binary on this machine: use the tool timeout and check exit codes. **One Lean process at a time**; do not
   kill processes you did not start.
6. **Section variables.** An instance-implicit section variable that the *statement* does not mention is not
   part of an `instance` or `def`; the elaborated signatures are in `scratch/signatures.txt`. If a proof
   seems to need a hypothesis that the signature lacks, read the sketch — it says which route avoids it
   (for example T002).
7. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each
   shows only `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
8. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
9. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it
   before acting, and delete it only if its `BOARD:` line names this board.
10. **Mathlib first.** Every name in a "Mathlib lemmas needed" block was checked by elaboration against the
    pinned Mathlib: `scratch/names_tickets_mathlib.lean` (443 names) and `scratch/names_tickets_chain.lean`
    (53 floor, chain and board names) are generated from those blocks by `scratch/extract_names.py`, and both
    elaborate with no error and no deprecation warning. `T0xx` in a sketch refers to an earlier ticket of this
    board. If Mathlib already has a ticket's statement, use it and record the name.
11. **Readable proofs** (user preference): explicit `ring` identities, `mul_nonneg`, `linarith` over opaque
    `nlinarith`; `omega`, not `lia`.
12. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; full table in `plan.md`)

E1 a Weierstrass polynomial is monic of Gauss norm one (BGR 5.2.3/1), **not** "non-leading coefficients of
norm `< 1`" (`X − 1`) · E2 the Tate algebra is the type `MvPowerSeries.Restricted K 1` of mathlib4#42867, and
its floor is in this chain · E3 the distinguished variable is `X 0` · E4 the maximum-modulus point has a
finite residue field by construction (no forward reference to §1.2.4) · E5 `dim Tₙ ≤ n` by integral descent
(Bosch 1.2/10), not BGR 7.1.1/3 · E6 closedness of ideals is proved here (Bosch 1.3), not cited · E7 the
§0.4.1 route is BGR 3.5.1/3–4 and 4.3/2 in characteristic zero; characteristic `p` is not on this board · E8
the relative form of Bosch 1.8/13 belongs to Layer 4 · E9 "`Q(T₁)` is not complete" belongs to Layer 2 · E10
substitution, evaluation and noetherianity are supplied by this layer · E11 `|f(x)|` is spelled
`spectralValue (minpoly K (mk f))` · E12 the chart example `X₁ − X₂` is already distinguished. E1–E12 are
applied to the roadmap README (uncommitted).

## Dependency order

The tickets below are listed in this order.

```text
G1  Basic            T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2
G2  Reduction        (CLEANUP-2) T006 → T007 → T008 → CLEANUP-3 → T009 → T010 → T011 → CLEANUP-4 → T012 → CLEANUP-5
G3  Eval             (CLEANUP-2) T013 → T014 → T015 → CLEANUP-6 → T016 → T017 → T018 → CLEANUP-7
G4  EvalReduction    (CLEANUP-5, CLEANUP-7) T019 → T020 → T021 → CLEANUP-8
G5  SupSeminorm      T022 → T023 → T024 → CLEANUP-9
G6  MaxModulus       T025 → (CLEANUP-5, CLEANUP-8) T026 → (CLEANUP-9) T027 → CLEANUP-ALL-1 → T028 [M1] → CLEANUP-10
G7  Distinguished    (CLEANUP-2) T029 → T030 → (CLEANUP-4) T031 → CLEANUP-11 → T032 → T033 → T034 → CLEANUP-12
G8  Finiteness       (CLEANUP-12) T035 → T036 → T037 → CLEANUP-13
G9  Chart            T038 → T039 → T040 → CLEANUP-14 → (CLEANUP-7) T041 → (CLEANUP-8) T042
                     → (CLEANUP-12) T043 → CLEANUP-15
G10 Rueckert         T044 → T045 → T046 → CLEANUP-16 → T047 → T048 → CLEANUP-17
G11 Tate/Rueckert    (CLEANUP-13, CLEANUP-15) T049 → CLEANUP-ALL-2 → T050 [M2] → CLEANUP-18
G12 Bald             T051 → T052 → T053 → CLEANUP-19 → T054 → CLEANUP-20
G13 Orthonormal      T055 → T056 → T057 → CLEANUP-21
G14 OrthonormalLift  (CLEANUP-20) T058 → (CLEANUP-21) T059 → T060 → CLEANUP-22 → T061 → CLEANUP-23
G15 StrictlyClosed   T062 → (CLEANUP-2, CLEANUP-21) T063 → (CLEANUP-5) T064 → CLEANUP-24
                     → (CLEANUP-23, CLEANUP-20) T065 → T066 → T067 → CLEANUP-25 → T068 → T069
                     → CLEANUP-ALL-3 → T070 [M3] → CLEANUP-26
G16 WeaklyStable     T071 → T072 → T073 → CLEANUP-27 → T074 → T075 → CLEANUP-28
G17 Japanese         T076 → CLEANUP-29
G18 Stable           (CLEANUP-18, CLEANUP-28, CLEANUP-29) CLEANUP-ALL-4 → T077 [M4] → CLEANUP-30
G19 Examples         (CLEANUP-15, CLEANUP-9) T078 → T079 → (CLEANUP-13) T080 → CLEANUP-31
End                  all final per-file cleanups → T081 (chain root) → CLEANUP-FINAL
```

Cleanup cadence: a `/cleanup` after every third proof ticket on a file and after the last one; a
`/cleanup-all` before each milestone; a final `/cleanup-all`. On `MaxModulus.lean` the pre-milestone sweep
`CLEANUP-ALL-1` is the mid-file cleanup.

---

## Tickets

### [T001] Gauss terms and truncations
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: none · **Parallel**: yes (with T002, G5, G10, G12, G13, G16, G17, T038) · **Type**: lemmas
- **Progress**: 2026-10-02T14:02: DONE — three proofs (floor's norm_le_iff, exists_achievesGaussNorm; truncations via Tendsto.eventually + Metric.ball_mem_nhds — rewriting HasSum/Metric.tendsto_atTop under the Restricted seam times out); module builds, standard axioms
- **Leaves**: L1.1, L1.2, L1.6

#### Statement
```lean
theorem norm_coeff_mul_prod_le (f : Restricted R c) (t : σ →₀ ℕ) :
    ‖coeff t f.1‖ * t.prod (c · ^ ·) ≤ ‖f‖ := by sorry
theorem exists_norm_eq_norm_coeff_mul_prod (f : Restricted R c) :
    ∃ t : σ →₀ ℕ, ‖f‖ = ‖coeff t f.1‖ * t.prod (c · ^ ·) := by sorry
theorem exists_finset_norm_sub_sum_monomial_lt (f : Restricted R c) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (σ →₀ ℕ), ‖f - ∑ t ∈ s, monomial c t (coeff t f.1)‖ < ε := by sorry
```
#### Proof sketch
1. `norm_coeff_mul_prod_le`: `exact (norm_le_iff c f).mp le_rfl t` (the floor's criterion).
2. `exists_norm_eq_norm_coeff_mul_prod`: `obtain ⟨t, ht⟩ := exists_achievesGaussNorm c f` and
   `exact ⟨t, (norm_def c f).trans ht.symm⟩` — the proof of the floor's `exists_coeff_ne_zero_norm_eq`
   without its `f ≠ 0`.
3. `exists_finset_norm_sub_sum_monomial_lt`: unfold `hasSum_monomial c f` exactly as the floor's own proof
   does (`rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]`), take the finset `s` it
   gives for `ε`, and rewrite `dist` to `‖f - ∑ …‖` with `dist_eq_norm`, `norm_sub_rev`.
#### Mathlib lemmas needed
Floor: `Restricted.norm_le_iff`, `Restricted.exists_achievesGaussNorm`, `Restricted.norm_def`, `Restricted.hasSum_monomial`. Mathlib: `Metric.tendsto_atTop`, `dist_eq_norm`, `norm_sub_rev`.
#### Sources
[BGR] 5.1.1, `bgr-5.1.md:27–36`; decomposition L1.1, L1.2, L1.6.
#### Generality decision
A normed ring `R` and an arbitrary polyradius `c` (the floor's generality). No `f ≠ 0` in item 2.

### [T002] Constants embed: nontriviality, characteristic zero, domain
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: none · **Parallel**: no (same file as T001) · **Type**: instances
- **Progress**: 2026-10-02T14:02: DONE — through the underlying power series (constantCoeff; Mathlib instance NoZeroDivisors (MvPowerSeries σ R), import RingTheory.MvPowerSeries.NoZeroDivisors; charZero_of_injective_ringHom, import Algebra.CharP.Algebra); standard axioms
- **Leaves**: L1.3, L1.4, L1.5

#### Statement
```lean
instance instNontrivial [Nontrivial R] : Nontrivial (Restricted R c) := by sorry
instance instCharZero [CharZero R] : CharZero (Restricted R c) := by sorry
instance instIsDomain [NormMulClass R] [Nontrivial R] : IsDomain (Restricted R c) := by sorry
```
#### Proof sketch
⚠ The elaborated statements carry **no** `Fact (∀ i, 0 < c i)` (checked in `scratch/signatures.txt`), so
the norm is not available; all three proofs go through the underlying power series.

1. `instNontrivial`: `⟨⟨0, 1, fun h ↦ zero_ne_one (α := R) ?_⟩⟩`, where the goal follows from
   `congrArg (fun f : Restricted R c ↦ MvPowerSeries.constantCoeff f.1) h` with `val_zero`, `val_one`,
   `map_zero`, `map_one`.
2. `instCharZero`: `charZero_of_injective_ringHom (f := C c) ?_`; injectivity: from `C c a = C c b` apply
   `congrArg (fun f ↦ MvPowerSeries.constantCoeff f.1)` and `val_C`, `MvPowerSeries.constantCoeff_C`.
   (`RingHom.charZero` goes the other way.)
3. `instIsDomain`: `haveI : NoZeroDivisors R := NormMulClass.toNoZeroDivisors`; then
   `NoZeroDivisors (Restricted R c)`: from `f * g = 0` get `f.1 * g.1 = 0` (`congrArg Subtype.val`-style
   through `val_mul`, `val_zero`), use Mathlib's instance `NoZeroDivisors (MvPowerSeries σ R)`, and return
   with `Restricted.ext`. Finish with `NoZeroDivisors.to_isDomain`.
#### Mathlib lemmas needed
`charZero_of_injective_ringHom`, `MvPowerSeries.constantCoeff_C`, `NormMulClass.toNoZeroDivisors`, `NoZeroDivisors.to_isDomain`, the instance `NoZeroDivisors (MvPowerSeries σ R)` (found by `inferInstance`). Floor: `Restricted.ext`, `val_zero`, `val_one`, `val_mul`, `val_C`.
#### Sources
[BGR] 5.1.2/1, `bgr-5.1.md:67`, `:84`; [Bo] `bosch-lectures.txt:376`; [RM] §0.1.4; decomposition L1.3–L1.5.
#### Generality decision
Every polyradius, no positivity. `instCharZero` is on `Restricted R c` because Mathlib already has `IsFractionRing.charZero`. `NormMulClass R` (not `NoZeroDivisors R`) in `instIsDomain`: it is the companion of the floor's `NormMulClass (Restricted R c)`.

### [T003] Polynomials are dense; the Gauss norm is a `K`-algebra norm
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: T001 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:02: DONE — density from T001 + toRestricted_monomial; norm_smul_eq by ≤ twice (inv_smul_smul₀); standard axioms
- **Leaves**: L1.7, L1.8

#### Statement
```lean
theorem denseRange_toRestricted : DenseRange (MvPolynomial.toRestricted (R := R) c) := by sorry
theorem norm_smul_eq (a : K) (f : Restricted K c) : ‖a • f‖ = ‖a‖ * ‖f‖ := by sorry
```
#### Proof sketch
1. `denseRange_toRestricted`: `rw [Metric.denseRange_iff]`; for `f`, `ε` take `s` from
   `exists_finset_norm_sub_sum_monomial_lt c f hε` (T001) and the polynomial
   `p := ∑ t ∈ s, MvPolynomial.monomial t (coeff t f.1)`; `map_sum` and `MvPolynomial.toRestricted_monomial`
   identify `toRestricted c p` with the truncation; `dist_eq_norm`.
2. `norm_smul_eq`: `le_antisymm`.
   - `≤`: `(norm_le_iff c _).mpr fun t ↦ ?_`; `val_smul`, `MvPowerSeries.coeff_smul`, `norm_mul`, `mul_assoc`,
     then `mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c f t) (norm_nonneg a)`.
   - `≥`: if `a = 0`, `simp`. Otherwise apply the `≤` just proved to `a⁻¹` and `a • f`:
     `‖f‖ = ‖a⁻¹ • a • f‖ ≤ ‖a‖⁻¹ * ‖a • f‖`, and clear the inverse (`le_inv_mul_iff₀`-style, or multiply by
     `‖a‖ > 0` and `linarith`).
   The instance `instNormedAlgebra` below it is already complete and uses this lemma.
#### Mathlib lemmas needed
`Metric.denseRange_iff`, `MvPowerSeries.coeff_smul`, `norm_mul`, `norm_inv`, `inv_smul_smul₀`, `mul_le_mul_of_nonneg_left`. Floor: `MvPolynomial.toRestricted_monomial`, `Restricted.val_smul`, `Restricted.norm_le_iff`.
#### Sources
[BGR] 5.1.1/1, `bgr-5.1.md:34–36`; [Bo] `bosch-lectures.txt:373`; decomposition L1.7, L1.8.
#### Generality decision
Density for a normed commutative ring (needed by `MvPolynomial`); the equality `‖a • f‖ = ‖a‖ * ‖f‖` for a normed field (over a ring only `≤` holds).

### [CLEANUP-1] Run /cleanup on `TateAlgebra/Basic.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:02: inline cleanup started · 2026-10-02T14:03: DONE inline — runLinter clean, widths ≤ 100, haveI→have in tactic mode, imports minimal (two added for T002 only)
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T004] The unit polyradius: the Gauss norm is the largest coefficient
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: CLEANUP-1 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:03: started · 2026-10-02T14:05: DONE — private prod_one_pow (simp [Finsupp.prod]) turns the floor's weighted criteria into coefficient criteria; standard axioms
- **Leaves**: L1.9–L1.12

#### Statement
```lean
theorem norm_coeff_le (f : Restricted R (1 : σ → ℝ)) (t : σ →₀ ℕ) : ‖coeff t f.1‖ ≤ ‖f‖ := by sorry
theorem exists_norm_coeff_eq (f : Restricted R (1 : σ → ℝ)) :
    ∃ t : σ →₀ ℕ, ‖coeff t f.1‖ = ‖f‖ := by sorry
theorem norm_le_iff_forall_norm_coeff_le {ε : ℝ} (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ ≤ ε ↔ ∀ t, ‖coeff t f.1‖ ≤ ε := by sorry
theorem norm_lt_iff_forall_norm_coeff_lt {ε : ℝ} (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ < ε ↔ ∀ t, ‖coeff t f.1‖ < ε := by sorry
```
#### Proof sketch
Private helper first: `prod_one_pow (t : σ →₀ ℕ) : t.prod ((1 : σ → ℝ) · ^ ·) = 1`
(`simp [Finsupp.prod]`: `Pi.one_apply`, `one_pow`, `Finset.prod_const_one`).

1. `norm_coeff_le`: `norm_coeff_mul_prod_le 1 f t` rewritten with the helper and `mul_one`.
2. `exists_norm_coeff_eq`: `exists_norm_eq_norm_coeff_mul_prod 1 f`, rewritten, `.symm`.
3. `norm_le_iff_forall_norm_coeff_le`: `(norm_le_iff 1 f).trans` and `simp only [helper, mul_one]`.
4. `norm_lt_iff_forall_norm_coeff_lt`: the same with the floor's `norm_lt_iff`.
#### Mathlib lemmas needed
`Finsupp.prod`, `Finset.prod_const_one`, `one_pow`. Floor: `Restricted.norm_le_iff`, `Restricted.norm_lt_iff`.
#### Sources
[BGR] 5.1.1, `bgr-5.1.md:29`; 5.1.2, `bgr-5.1.md:74–75`; [RM] §0.1.2; decomposition L1.9–L1.12.
#### Generality decision
Any index type `σ` and any normed ring. These four lemmas are the only place the product `1 ^ t` is simplified; everything later uses them.

### [T005] `|Tₙ| = |K|` and normalisation
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: T004 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:05: DONE — f.2 read as the nullity of the Gauss terms; normalisation by the inverse of a maximal coefficient; standard axioms
- **Leaves**: L1.13–L1.16

#### Statement
```lean
theorem tendsto_norm_coeff_cofinite (f : Restricted R (1 : σ → ℝ)) :
    Tendsto (fun t ↦ ‖coeff t f.1‖) cofinite (𝓝 0) := by sorry
theorem finite_setOf_le_norm_coeff (f : Restricted R (1 : σ → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    {t | ε ≤ ‖coeff t f.1‖}.Finite := by sorry
theorem norm_mem_range_norm (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ ∈ Set.range (norm : R → ℝ) := by sorry
theorem exists_norm_smul_eq_one {f : Restricted K (1 : σ → ℝ)} (hf : f ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ‖a • f‖ = 1 := by sorry
```
#### Proof sketch
1. `tendsto_norm_coeff_cofinite`: `f.2` is the defining `Tendsto (fun t ↦ ‖coeff t f.1‖ * t.prod (1 · ^ ·))
   cofinite (𝓝 0)`; `refine f.2.congr fun t ↦ ?_` and the helper of T004 (the floor reads `f.2` the same way
   in `hasSum_monomial`).
2. `finite_setOf_le_norm_coeff`: `have h := (tendsto_norm_coeff_cofinite f).eventually_lt_const hε`;
   `rw [Filter.eventually_cofinite] at h`; `exact h.subset fun t ht ↦ not_lt.2 ht`.
3. `norm_mem_range_norm`: `obtain ⟨t, ht⟩ := exists_norm_coeff_eq f; exact ⟨_, ht⟩`.
4. `exists_norm_smul_eq_one`: `obtain ⟨t, ht⟩ := exists_norm_coeff_eq f`; `‖coeff t f.1‖ = ‖f‖ ≠ 0`, so
   `a := (coeff t f.1)⁻¹ ≠ 0`; `norm_smul_eq`, `norm_inv`, `ht`, `inv_mul_cancel₀`.
#### Mathlib lemmas needed
`Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`, `Set.Finite.subset`, `norm_inv`, `inv_mul_cancel₀`, `norm_ne_zero_iff`.
#### Sources
[BGR] 5.1.1, `bgr-5.1.md:18–19`, `:38–41` (Observation 2); decomposition L1.13–L1.16.
#### Generality decision
Items 1–3 for a normed ring; item 4 for a normed field, with `a ≠ 0` recorded because the scaling is undone later (T026, T043).

### [CLEANUP-2] Run /cleanup on `TateAlgebra/Basic.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Basic.lean` · **Depends on**: T005 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:05: DONE inline — Basic.lean sorry-free, runLinter clean, widths ≤ 100, module docstring lists the final names
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T006] The reduced coefficients form a polynomial; additive laws
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G3) · **Type**: lemmas
- **Progress**: 2026-10-02T14:05: started · 2026-10-02T14:11: DONE — private residue_unitBallCoeff_eq_zero_iff; laws by MvPolynomial.ext + Subtype.ext/simp; standard axioms
- **Leaves**: L2.1, L2.2, L2.4, L2.5

#### Statement
```lean
theorem finite_support_residue_unitBallCoeff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    (Function.support fun t ↦ residue (unitClosedBall K) (unitBallCoeff f t)).Finite := by sorry
theorem reductionFun_one :
    reductionFun (1 : unitClosedBall (Restricted K (1 : σ → ℝ))) = 1 := by sorry
theorem reductionFun_zero :
    reductionFun (0 : unitClosedBall (Restricted K (1 : σ → ℝ))) = 0 := by sorry
theorem reductionFun_add (f g : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionFun (f + g) = reductionFun f + reductionFun g := by sorry
```
#### Proof sketch
Private helper: `residue_unitBallCoeff_eq_zero_iff (f) (t) :
residue _ (unitBallCoeff f t) = 0 ↔ ‖coeff t f.1.1‖ < 1` — `residue_eq_zero_iff`,
`maximalIdeal_unitClosedBall`, `mem_openUnitBallIdeal`, `coe_unitBallCoeff`.

1. `finite_support_residue_unitBallCoeff`: `(finite_setOf_le_norm_coeff f.1 one_pos).subset fun t ht ↦ ?_`;
   `ht` says the residue is nonzero, so by the helper `¬ ‖coeff t f.1.1‖ < 1`, i.e. `1 ≤ ‖…‖`.
2. `reductionFun_zero`, `_one`, `_add`: `MvPolynomial.ext _ _ fun t ↦ ?_`, `coeff_reductionFun`; the element
   `unitBallCoeff (f + g) t` equals `unitBallCoeff f t + unitBallCoeff g t` by `Subtype.ext` (`val_add`,
   `map_add`), similarly for `0` and `1` (`MvPowerSeries.coeff_one`, an `if` on `t = 0`, matched with
   `MvPolynomial.coeff_one`); then `map_add`, `map_zero`, `map_one` of `residue`.
#### Mathlib lemmas needed
`IsLocalRing.residue_eq_zero_iff`, `MvPolynomial.ext`, `MvPolynomial.coeff_one`, `MvPolynomial.coeff_add`, `MvPowerSeries.coeff_one`, `Finsupp.ofSupportFinite_coe`. Chain: `NormedRing.maximalIdeal_unitClosedBall`, `NormedRing.mem_openUnitBallIdeal`.
#### Sources
[BGR] 5.1.2, `bgr-5.1.md:78–83`; [Bo] `bosch-lectures.txt:382–389`; decomposition L2.1, L2.2, L2.4, L2.5.
#### Generality decision
Any normed field (no completeness, trivial valuation allowed) and any `σ`.

### [T007] The reduction is multiplicative
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-02T14:11: DONE — unitBallCoeff of a product is the antidiagonal sum (Subtype.ext + MvPowerSeries.coeff_mul), then map_sum/map_mul; standard axioms
- **Leaves**: L2.3

#### Statement
```lean
theorem reductionFun_mul (f g : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionFun (f * g) = reductionFun f * reductionFun g := by sorry
```
#### Proof sketch
`MvPolynomial.ext _ _ fun t ↦ ?_`; `coeff_reductionFun`, `MvPolynomial.coeff_mul`. On the left,
`coeff t (f * g).1.1 = ∑ p ∈ Finset.antidiagonal t, coeff p.1 f.1.1 * coeff p.2 g.1.1`
(`val_mul`, `MvPowerSeries.coeff_mul`), so
`unitBallCoeff (f * g) t = ∑ p ∈ antidiagonal t, unitBallCoeff f p.1 * unitBallCoeff g p.2` by `Subtype.ext`
(push the coercion through the sum with `AddSubmonoidClass.coe_finsetSum`). Then
`map_sum`, `map_mul` and `coeff_reductionFun` again.
#### Mathlib lemmas needed
`MvPolynomial.coeff_mul`, `MvPowerSeries.coeff_mul`, `map_sum`, `map_mul`, `AddSubmonoidClass.coe_finsetSum`.
#### Sources
[Bo] `bosch-lectures.txt:384–385` (`π` is an epimorphism of rings); decomposition L2.3.
#### Generality decision
As T006. Both antidiagonals are over `σ →₀ ℕ`, so no reindexing is needed.

### [T008] The kernel of the reduction
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T007 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: DONE — as sketched; standard axioms
- **Leaves**: L2.6–L2.8

#### Statement
```lean
theorem reduction_eq_zero_iff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction f = 0 ↔ ‖(f : Restricted K (1 : σ → ℝ))‖ < 1 := by sorry
theorem norm_eq_one_of_reduction_ne_zero {f : unitClosedBall (Restricted K (1 : σ → ℝ))}
    (hf : reduction f ≠ 0) : ‖(f : Restricted K (1 : σ → ℝ))‖ = 1 := by sorry
theorem ker_reduction :
    RingHom.ker (reduction (K := K) (σ := σ)) = openUnitBallIdeal (Restricted K (1 : σ → ℝ)) := by sorry
```
#### Proof sketch
1. `reduction_eq_zero_iff`: `rw [MvPolynomial.ext_iff]`; `simp only [coeff_reduction, MvPolynomial.coeff_zero]`;
   the helper of T006 turns each condition into `‖coeff t f.1.1‖ < 1`; conclude with
   `(norm_lt_iff_forall_norm_coeff_lt f.1).symm`.
2. `norm_eq_one_of_reduction_ne_zero`: `le_antisymm (Subring.norm_le_one f) (not_lt.1 fun h ↦ hf ((reduction_eq_zero_iff f).2 h))`.
3. `ker_reduction`: `Ideal.ext fun f ↦ ?_`; `RingHom.mem_ker`, item 1, `mem_openUnitBallIdeal`.
#### Mathlib lemmas needed
`MvPolynomial.ext_iff`, `MvPolynomial.coeff_zero`, `RingHom.mem_ker`. Chain: `Subring.norm_le_one`, `NormedRing.mem_openUnitBallIdeal`.
#### Sources
[BGR] `bgr-5.1.md:83`; [Bo] `bosch-lectures.txt:390–391`; [RM] §0.1.2; decomposition L2.6–L2.8.
#### Generality decision
As T006.

### [CLEANUP-3] Run /cleanup on `TateAlgebra/Reduction.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T008 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:11: DONE inline — runLinter clean on Reduction; widths fixed
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T009] Surjectivity: polynomials over the unit ball
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: CLEANUP-3 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: DONE — private coeff_toRestricted_map_subtype; reductionEquiv_mk is rfl; congr 1 closes reduction_ofUnitBallPolynomial; coercions must be written (↑(p.coeff t) : K); standard axioms
- **Leaves**: L2.9–L2.13

#### Statement
```lean
theorem norm_toRestricted_map_subtype_le_one (p : MvPolynomial σ (unitClosedBall K)) :
    ‖MvPolynomial.toRestricted (1 : σ → ℝ) (MvPolynomial.map (unitClosedBall K).subtype p)‖ ≤ 1 := by sorry
theorem reduction_ofUnitBallPolynomial (p : MvPolynomial σ (unitClosedBall K)) :
    reduction (ofUnitBallPolynomial p) = MvPolynomial.map (residue (unitClosedBall K)) p := by sorry
theorem exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    ∃ p : MvPolynomial σ (unitClosedBall K),
      f - ofUnitBallPolynomial p ∈ openUnitBallIdeal (Restricted K (1 : σ → ℝ)) := by sorry
theorem reduction_surjective : Function.Surjective (reduction (K := K) (σ := σ)) := by sorry
theorem reductionEquiv_mk (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionEquiv (Ideal.Quotient.mk _ f) = reduction f := by sorry
```
#### Proof sketch
Private helper: `coeff_toRestricted_map_subtype (p) (t) :
coeff t (MvPolynomial.toRestricted 1 (MvPolynomial.map (unitClosedBall K).subtype p)).1 = (p.coeff t : K)` —
`MvPolynomial.val_toRestricted`, `MvPolynomial.coeff_coe`, `MvPolynomial.coeff_map`.

1. `norm_toRestricted_map_subtype_le_one`: `(norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ ?_`; helper;
   `Subring.norm_le_one`.
2. `reduction_ofUnitBallPolynomial`: `MvPolynomial.ext`; `coeff_reduction`, `MvPolynomial.coeff_map`; the two
   elements of `K⁰` agree by `Subtype.ext` and the helper (`coe_ofUnitBallPolynomial`).
3. `exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal`: `s := (finite_setOf_le_norm_coeff f.1 one_pos).toFinset`,
   `p := ∑ t ∈ s, MvPolynomial.monomial t (unitBallCoeff f t)`; `mem_openUnitBallIdeal` and
   `norm_lt_iff_forall_norm_coeff_lt`: the coefficient of the difference at `t` is `0` for `t ∈ s` and
   `coeff t f` (of norm `< 1`) otherwise (`MvPolynomial.coeff_sum`, `coeff_monomial`, `Finset.sum_ite_eq`).
4. `reduction_surjective`: for `q`, `obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ residue_surjective q`;
   `exact ⟨ofUnitBallPolynomial p, reduction_ofUnitBallPolynomial p⟩`.
5. `reductionEquiv_mk`: `rfl`, or `simp [reductionEquiv, Ideal.quotEquivOfEq_mk]` with
   `RingHom.quotientKerEquivOfSurjective_apply_mk`.
#### Mathlib lemmas needed
`MvPolynomial.coeff_coe`, `MvPolynomial.coeff_map`, `MvPolynomial.map_surjective`, `IsLocalRing.residue_surjective`, `Ideal.quotEquivOfEq_mk`, `RingHom.quotientKerEquivOfSurjective`, `MvPolynomial.coeff_monomial`, `Finset.sum_ite_eq`. Floor: `MvPolynomial.val_toRestricted`.
#### Sources
[BGR] 5.1.2/2, `bgr-5.1.md:69`, `:83`; `bgr-5.2.md:78–82`; [Bo] `bosch-lectures.txt:382–385`; decomposition L2.9–L2.13.
#### Generality decision
Item 3 (`T⁰ = K⁰[X] + T⁰⁰`) is stated separately because T020 and T021 consume it.

### [T010] Power-bounded and topologically nilpotent series
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: DONE — one-line transfers of the PFA criteria; standard axioms
- **Leaves**: L2.14, L2.15

#### Statement
```lean
theorem isPowerBounded_iff_forall_norm_coeff_le_one {f : Restricted 𝕜 (1 : σ → ℝ)} :
    PowerBounded.IsPowerBounded f ↔ ∀ t, ‖coeff t f.1‖ ≤ 1 := by sorry
theorem isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one {f : Restricted K (1 : σ → ℝ)} :
    IsTopologicallyNilpotent f ↔ ∀ t, ‖coeff t f.1‖ < 1 := by sorry
```
#### Proof sketch
1. `isPowerBounded_iff_forall_norm_coeff_le_one`:
   `PowerBounded.isPowerBounded_iff_norm_le_one.trans (norm_le_iff_forall_norm_coeff_le f)`. The chain lemma
   needs `[NormMulClass (Restricted 𝕜 1)]` (floor instance) and `[NeBot (𝓝[≠] (0 : Restricted 𝕜 1))]`
   (floor instance from `NeBot (𝓝[≠] (0 : 𝕜))`, which is `NormedField.nhdsNE_neBot`).
2. `isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one`:
   `isTopologicallyNilpotent_iff_norm_lt_one.trans (norm_lt_iff_forall_norm_coeff_lt f)`.
#### Mathlib lemmas needed
`NormedField.nhdsNE_neBot`. Chain: `PowerBounded.isPowerBounded_iff_norm_le_one`, `isTopologicallyNilpotent_iff_norm_lt_one`.
#### Sources
[BGR] 5.1.2, `bgr-5.1.md:86` (`T̊ₙ = Tₙ°`, `Ťₙ = Tₙˇ`); [RM] §0.1.2; decomposition L2.14, L2.15.
#### Generality decision
Power-boundedness over a nontrivially normed field (the chain lemma's hypothesis; [RM] convention 1); topological nilpotence over any normed field.

### [T011] Units of the Tate algebra and of its unit ball
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T010 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: DONE — IsUnit.map along Subring.subtype fails to synthesize MonoidHomClass on unitClosedBall (Restricted K 1): build the unit by hand with explicit Subtype.val fields; standard axioms
- **Leaves**: L2.16–L2.18

#### Statement
```lean
theorem isUnit_iff_norm_coeff_lt {f : Restricted K (1 : σ → ℝ)} :
    IsUnit f ↔ coeff 0 f.1 ≠ 0 ∧ ∀ t ≠ 0, ‖coeff t f.1‖ < ‖coeff 0 f.1‖ := by sorry
theorem isUnit_iff_isUnit_reduction (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    IsUnit f ↔ IsUnit (reduction f) := by sorry
theorem isUnit_coe_iff_isUnit_reduction {f : unitClosedBall (Restricted K (1 : σ → ℝ))}
    (hf : ‖(f : Restricted K (1 : σ → ℝ))‖ = 1) :
    IsUnit (f : Restricted K (1 : σ → ℝ)) ↔ IsUnit (reduction f) := by sorry
```
#### Proof sketch
1. `isUnit_iff_norm_coeff_lt`: `rw [Restricted.isUnit_iff]` (floor, `c = 1`), then
   `constantCoeff_eq_coeff_zero`, `isUnit_iff_ne_zero`, and the helper `prod_one_pow` of T004 inside the
   `∀ t ≠ 0` (use `forall_congr'`).
2. `isUnit_iff_isUnit_reduction`: `(NormedRing.isUnit_iff_isUnit_mk f).trans ?_`; then
   `rw [← reductionEquiv_mk]` and `(isUnit_map_iff reductionEquiv _).symm` (the `IsLocalHom` instance of an
   equivalence is `isLocalHom_equiv`).
3. `isUnit_coe_iff_isUnit_reduction`: `←`: item 2 and `IsUnit.map (unitClosedBall _).subtype`. `→`: from
   `hu : IsUnit (f : T)` get `g` with `f * g = 1`; `norm_mul`, `hf`, `norm_one` give `‖g‖ = 1`, so
   `g ∈ unitClosedBall _`; build the unit of `T⁰` (`isUnit_iff_exists_inv`, `Subtype.ext`) and use item 2.
#### Mathlib lemmas needed
`isUnit_iff_ne_zero`, `isUnit_map_iff`, `isLocalHom_equiv`, `IsUnit.map`, `isUnit_iff_exists_inv`, `norm_mul`, `norm_one`. Floor: `Restricted.isUnit_iff`, `Restricted.constantCoeff_eq_coeff_zero`. Chain: `NormedRing.isUnit_iff_isUnit_mk`.
#### Sources
[BGR] 5.1.3/1, `bgr-5.1.md:96–104`; [Bo] 1.2/4, `bosch-lectures.txt:431–441`; decomposition L2.16–L2.18.
#### Generality decision
`K` complete. `coeff 0 f.1 ≠ 0` is a separate conjunct so that the statement is right for `σ` empty. Item 3 needs `‖f‖ = 1` (`f = p` is a unit of `T` with reduction `0`).

### [CLEANUP-4] Run /cleanup on `TateAlgebra/Reduction.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T011 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:11: DONE inline — lint clean, widths ≤ 100
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T012] The Jacobson radical of the Tate algebra is zero
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: CLEANUP-4 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: DONE — BGR's two cases; jacobson via mem_jacobson_bot + linear_combination; standard axioms
- **Leaves**: L2.19, L2.20

#### Statement
```lean
theorem exists_norm_eq_one_not_isUnit_C_add {f : Restricted K (1 : σ → ℝ)} (hf : ‖f‖ = 1) :
    ∃ a : K, ‖a‖ = 1 ∧ ¬ IsUnit (C (1 : σ → ℝ) a + f) := by sorry
theorem jacobson_bot : Ideal.jacobson (⊥ : Ideal (Restricted K (1 : σ → ℝ))) = ⊥ := by sorry
```
#### Proof sketch
1. `exists_norm_eq_one_not_isUnit_C_add` (BGR's two cases; `a₀ := coeff 0 f.1`, `‖a₀‖ ≤ 1` by
   `norm_coeff_le`).
   - `‖a₀‖ < 1`: take `a = 1`. By `exists_norm_coeff_eq f` there is `t` with `‖coeff t f.1‖ = 1`, and `t ≠ 0`.
     The constant coefficient of `C 1 1 + f` is `1 + a₀`, of norm `1`
     (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), and its coefficient at `t` is `coeff t f.1`
     (`val_add`, `val_C`, `MvPowerSeries.coeff_C`, `if_neg`), of norm `1`: the strict inequality of
     `isUnit_iff_norm_coeff_lt` fails at `t`.
   - `‖a₀‖ = 1`: take `a = -a₀`; the constant coefficient of `C 1 (-a₀) + f` is `0`, so it is not a unit by
     `isUnit_iff_norm_coeff_lt`.
2. `jacobson_bot`: `eq_bot_iff.2 fun f hf ↦ ?_`; by contradiction assume `f ≠ 0`. Take `a ≠ 0` with
   `‖a • f‖ = 1` (`exists_norm_smul_eq_one`); `a • f = C 1 a * f` lies in `jacobson ⊥` (ideal). Take `c`
   from item 1 for `a • f`; `c ≠ 0`. `Ideal.mem_jacobson_bot` at `y := C 1 c⁻¹` gives
   `IsUnit (a • f * C 1 c⁻¹ + 1)`, and `a • f * C 1 c⁻¹ + 1 = C 1 c⁻¹ * (C 1 c + a • f)` with `C 1 c⁻¹` a
   unit — contradiction.
#### Mathlib lemmas needed
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `MvPowerSeries.coeff_C`, `Ideal.mem_jacobson_bot`, `IsUnit.mul_iff`, `Algebra.smul_def`. Floor: `Restricted.algebraMap_apply`, `Restricted.val_C`.
#### Sources
[BGR] 5.1.3/2–3, `bgr-5.1.md:108–124`; decomposition L2.19, L2.20.
#### Generality decision
Any index type `σ` (no finiteness). Only the forward half of the unit criterion is used.

### [CLEANUP-5] Run /cleanup on `TateAlgebra/Reduction.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Reduction.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:11: DONE inline — Reduction.lean sorry-free, runLinter clean, widths ≤ 100, proof of the K⁰[X]+T⁰⁰ lemma tidied
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T013] The evaluated series converges
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G2) · **Type**: lemmas
- **Progress**: 2026-10-02T14:11: started · 2026-10-02T14:19: DONE — the Fact (∀ i, 0 < c i) section variable was unused by everything except norm/continuity statements: scoped it to norm_eval₂_le, continuous_eval₂, norm_aeval_le, continuous_aeval (stronger statements; whole board rebuilt, 2722 jobs); standard axioms
- **Leaves**: L3.1–L3.3

#### Statement
```lean
omit [IsUltrametricDist R] [IsUltrametricDist B] in
theorem norm_map_mul_prod_pow_le (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (hx : ∀ i, ‖x i‖ ≤ c i) (a : R)
    (t : σ →₀ ℕ) : ‖φ a * t.prod fun i k ↦ x i ^ k‖ ≤ ‖a‖ * t.prod (c · ^ ·) := by sorry
omit [IsUltrametricDist B] in
theorem tendsto_map_coeff_mul_prod_pow (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (hx : ∀ i, ‖x i‖ ≤ c i)
    (f : Restricted R c) :
    Tendsto (fun t : σ →₀ ℕ ↦ φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k) cofinite (𝓝 0) := by sorry
theorem summable_map_coeff_mul_prod_pow [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hx : ∀ i, ‖x i‖ ≤ c i) (f : Restricted R c) :
    Summable fun t : σ →₀ ℕ ↦ φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k := by sorry
```
#### Proof sketch
1. `norm_map_mul_prod_pow_le`: `B` has no `NormOneClass`, so split on `t`.
   - `t = 0`: `Finsupp.prod_zero_index`, `mul_one` on both sides, `hφ a`.
   - `t ≠ 0`: `(norm_mul_le _ _).trans (mul_le_mul (hφ a) ?_ (norm_nonneg _) (norm_nonneg _))`, and for the
     product (`Finsupp.prod` is a `Finset.prod` over the nonempty `t.support`):
     `Finset.norm_prod_le'` (nonempty), then `Finset.prod_le_prod` with, on the support (where `0 < t i`),
     `norm_pow_le'` and `pow_le_pow_left₀ (norm_nonneg _) (hx i)`.
2. `tendsto_map_coeff_mul_prod_pow`: `squeeze_zero_norm' (Filter.Eventually.of_forall fun t ↦ ?_) f.2` with
   item 1 (`f.2` is the nullity of the Gauss terms).
3. `summable_map_coeff_mul_prod_pow`:
   `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_map_coeff_mul_prod_pow c φ x hφ hx f)`.
#### Mathlib lemmas needed
`Finset.norm_prod_le'`, `norm_pow_le'`, `pow_le_pow_left₀`, `Finset.prod_le_prod`, `Finsupp.prod_zero_index`, `squeeze_zero_norm'`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.
#### Sources
[BGR] 5.1.4, `bgr-5.1.md:219–223`, `:253`; decomposition L3.1–L3.3.
#### Generality decision
A contractive ring homomorphism `φ : R →+* B` into a normed commutative ring and any polyradius; `B` complete and ultrametric only for summability. No `NormOneClass B`.

### [T014] Evaluation: zero, one, addition
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T013 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:19: DONE — tsum_eq_single / Summable.tsum_add; standard axioms
- **Leaves**: L3.4–L3.6

#### Statement
```lean
omit [IsUltrametricDist B] hc in
theorem eval₂Fun_zero : eval₂Fun c φ x 0 = 0 := by sorry
omit [IsUltrametricDist B] hc in
theorem eval₂Fun_one : eval₂Fun c φ x 1 = 1 := by sorry
theorem eval₂Fun_add [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (hx : ∀ i, ‖x i‖ ≤ c i)
    (f g : Restricted R c) : eval₂Fun c φ x (f + g) = eval₂Fun c φ x f + eval₂Fun c φ x g := by sorry
```
#### Proof sketch
1. `eval₂Fun_zero`: `simp [eval₂Fun]` (`val_zero`, `map_zero`, `zero_mul`, `tsum_zero`).
2. `eval₂Fun_one`: `unfold eval₂Fun`; `rw [tsum_eq_single 0]`; at `0`: `val_one`, `MvPowerSeries.coeff_one`,
   `map_one`, `Finsupp.prod_zero_index`, `mul_one`; for `t ≠ 0` the coefficient is `0`. No summability is
   needed, which is why the statement has no hypothesis.
3. `eval₂Fun_add`: `unfold eval₂Fun`; rewrite the summand with `val_add`, `map_add`, `add_mul`;
   `Summable.tsum_add` with `summable_map_coeff_mul_prod_pow` twice.
#### Mathlib lemmas needed
`tsum_eq_single`, `tsum_zero`, `Summable.tsum_add`, `MvPowerSeries.coeff_one`, `Finsupp.prod_zero_index`.
#### Sources
[BGR] 5.1.3/5, `bgr-5.1.md:153–155`; decomposition L3.4–L3.6.
#### Generality decision
As T013.

### [T015] Evaluation is multiplicative (Cauchy product)
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T013 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-02T14:19: DONE — Mathlib's Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal with product summability from the chain's IsUltrametricDist.summable_prod_map₂ (ascribing the type of that  timed out at whnf; leaving it inferred works); Finsupp.prod_add_index' + ring; standard axioms
- **Leaves**: L3.7

#### Statement
```lean
theorem eval₂Fun_mul [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (hx : ∀ i, ‖x i‖ ≤ c i)
    (f g : Restricted R c) : eval₂Fun c φ x (f * g) = eval₂Fun c φ x f * eval₂Fun c φ x g := by sorry
```
#### Proof sketch
Add `import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums` to the file (Mathlib's
`Summable.mul_of_nonarchimedean` needs a `NonarchimedeanRing` instance that an ultrametric normed ring
does not have at the pin).

Write `u f t := φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k`.
1. `hf : Summable (u f)`, `hg : Summable (u g)` (T013), and
   `hfg : Summable fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ u f p.1 * u g p.2` from
   `IsUltrametricDist.summable_prod_map₂ (b := (· * ·)) norm_mul_le hf hg`.
2. `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg :
   (∑' t, u f t) * ∑' t, u g t = ∑' t, ∑ p ∈ Finset.antidiagonal t, u f p.1 * u g p.2`.
3. Termwise, `u (f * g) t = ∑ p ∈ antidiagonal t, u f p.1 * u g p.2`: `val_mul`, `MvPowerSeries.coeff_mul`,
   `map_sum`, `map_mul`, `Finset.sum_mul`, and for `p ∈ antidiagonal t` (`p.1 + p.2 = t`):
   `Finsupp.prod_add_index'` (with `pow_zero`, `pow_add`) to split `x ^ t`; reorder with `mul_mul_mul_comm`.
4. `tsum_congr` and item 2.
#### Mathlib lemmas needed
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, `MvPowerSeries.coeff_mul`, `Finsupp.prod_add_index'`, `Finset.mem_antidiagonal`, `mul_mul_mul_comm`, `tsum_congr`. Chain: `IsUltrametricDist.summable_prod_map₂`.
#### Sources
[BGR] 5.1.3/5, `bgr-5.1.md:153–155`; the Cauchy product, `bgr-2.md:56–59`; decomposition L3.7.
#### Generality decision
Commutativity of `B` is used to reorder `x ^ p.1 * φ b`. This is the one substantial computation of the file.

### [CLEANUP-6] Run /cleanup on `TateAlgebra/Eval.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T015 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:19: DONE inline — lint clean
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T016] Values, contraction and continuity of `eval₂`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: CLEANUP-6 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:19: DONE — as sketched; standard axioms
- **Leaves**: L3.8–L3.13

#### Statement
```lean
theorem eval₂_monomial (t : σ →₀ ℕ) (a : R) :
    eval₂ c φ x hφ hx (monomial c t a) = φ a * t.prod fun i k ↦ x i ^ k := by sorry
theorem eval₂_C (a : R) : eval₂ c φ x hφ hx (C c a) = φ a := by sorry
theorem eval₂_X (i : σ) : eval₂ c φ x hφ hx (X R c i) = x i := by sorry
theorem eval₂_toRestricted (p : MvPolynomial σ R) :
    eval₂ c φ x hφ hx (MvPolynomial.toRestricted c p) = MvPolynomial.eval₂ φ x p := by sorry
theorem norm_eval₂_le (f : Restricted R c) : ‖eval₂ c φ x hφ hx f‖ ≤ ‖f‖ := by sorry
theorem continuous_eval₂ : Continuous (eval₂ c φ x hφ hx) := by sorry
```
#### Proof sketch
1. `eval₂_monomial`: `rw [eval₂_apply, tsum_eq_single t]`; `val_monomial`, `MvPowerSeries.coeff_monomial`
   (`if_pos rfl` at `t`, `if_neg`, `map_zero`, `zero_mul` elsewhere).
2. `eval₂_C`: the same with `val_C`, `MvPowerSeries.coeff_C`, and `Finsupp.prod_zero_index`, `mul_one` at `0`.
3. `eval₂_X`: `val_X`, `MvPowerSeries.coeff_X`, the single term at `Finsupp.single i 1`;
   `Finsupp.prod_single_index (pow_zero _)`, `pow_one`, `map_one`, `one_mul`.
4. `eval₂_toRestricted`: prove `(eval₂ c φ x hφ hx).comp (MvPolynomial.toRestricted c) = MvPolynomial.eval₂Hom φ x`
   by `MvPolynomial.ringHom_ext` (`toRestricted_C`, `toRestricted_X`, items 2–3, `MvPolynomial.eval₂_C`,
   `eval₂_X`), then `RingHom.congr_fun`.
5. `norm_eval₂_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f) fun t ↦
   (norm_map_mul_prod_pow_le c φ x hφ hx _ t).trans (norm_coeff_mul_prod_le c f t)`.
6. `continuous_eval₂`: `AddMonoidHomClass.continuous_of_bound _ 1 fun f ↦ by rw [one_mul]; exact norm_eval₂_le hφ hx f`.
#### Mathlib lemmas needed
`tsum_eq_single`, `MvPowerSeries.coeff_monomial`, `MvPowerSeries.coeff_C`, `MvPowerSeries.coeff_X`, `Finsupp.prod_single_index`, `MvPolynomial.ringHom_ext`, `MvPolynomial.eval₂_C`, `MvPolynomial.eval₂_X`, `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, `AddMonoidHomClass.continuous_of_bound`. Floor: `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`.
#### Sources
[BGR] 5.1.3/5, `bgr-5.1.md:150–155`; 5.1.4/2, `bgr-5.1.md:250–255`; decomposition L3.8–L3.13.
#### Generality decision
Continuity is of the homomorphism `f ↦ f(x)`; continuity in `x` is not claimed.

### [T017] A continuous homomorphism is determined on constants and variables
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T003 · **Parallel**: no (same file as T013–T016) · **Type**: lemmas
- **Progress**: 2026-10-02T14:19: DONE — DenseRange.equalizer with MvPolynomial.ringHom_ext; standard axioms
- **Leaves**: L3.14, L3.19

#### Statement
```lean
theorem ringHom_ext_of_continuous {ψ₁ ψ₂ : Restricted R c →+* B} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) (hC : ∀ a, ψ₁ (C c a) = ψ₂ (C c a))
    (hX : ∀ i, ψ₁ (X R c i) = ψ₂ (X R c i)) : ψ₁ = ψ₂ := by sorry
theorem algHom_ext_of_continuous {ψ₁ ψ₂ : Restricted K c →ₐ[K] B} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) (hX : ∀ i, ψ₁ (X K c i) = ψ₂ (X K c i)) : ψ₁ = ψ₂ := by sorry
```
#### Proof sketch
1. `ringHom_ext_of_continuous`: `DFunLike.coe_injective ?_`, then
   `(denseRange_toRestricted c).equalizer h₁ h₂ (funext fun p ↦ ?_)`; the pointwise goal is
   `RingHom.congr_fun (MvPolynomial.ringHom_ext (f := ψ₁.comp (MvPolynomial.toRestricted c))
   (g := ψ₂.comp (MvPolynomial.toRestricted c)) ?_ ?_) p`, with the two goals closed by `toRestricted_C`,
   `hC` and `toRestricted_X`, `hX`.
2. `algHom_ext_of_continuous`: `AlgHom.coe_ringHom_injective` (or `AlgHom.ext` after `RingHom.congr_fun`) of
   item 1 applied to the underlying ring homomorphisms; `hC a` is
   `by rw [← algebraMap_apply]; simp [AlgHom.commutes]`.
#### Mathlib lemmas needed
`DenseRange.equalizer`, `MvPolynomial.ringHom_ext`, `AlgHom.commutes`, `AlgHom.coe_ringHom_injective`. Floor: `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`, `Restricted.algebraMap_apply`.
#### Sources
[BGR] 5.1.3/5, `bgr-5.1.md:151–153`; decomposition L3.14, L3.19.
#### Generality decision
The target is any Hausdorff topological semiring; continuity is a hypothesis (BGR's automatic continuity, 5.1.3/4, is specific to Tate algebras and is not on the board).

### [T018] Evaluation as a `K`-algebra homomorphism
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T016 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:19: DONE — the contraction proof (norm_algebraMap').le must be passed explicitly (not inferable); standard axioms
- **Leaves**: L3.15–L3.18

#### Statement
```lean
theorem aeval_X (i : σ) : aeval c x hx (X K c i) = x i := by sorry
theorem aeval_toRestricted (p : MvPolynomial σ K) :
    aeval c x hx (MvPolynomial.toRestricted c p) = MvPolynomial.aeval x p := by sorry
theorem norm_aeval_le (f : Restricted K c) : ‖aeval c x hx f‖ ≤ ‖f‖ := by sorry
theorem continuous_aeval : Continuous (aeval (K := K) c x hx) := by sorry
```
#### Proof sketch
`aeval c x hx f` is definitionally `eval₂ c (algebraMap K B) x _ hx f`.
1. `aeval_X`: `eval₂_X _ hx i`.
2. `aeval_toRestricted`: `(eval₂_toRestricted _ hx p).trans (MvPolynomial.aeval_def x p).symm` (after
   `MvPolynomial.coe_eval₂Hom` if needed).
3. `norm_aeval_le`: `norm_eval₂_le _ hx f`.
4. `continuous_aeval`: `continuous_eval₂ _ hx`.
#### Mathlib lemmas needed
`MvPolynomial.aeval_def`, `norm_algebraMap'`.
#### Sources
[BGR] 5.1.3/5, 5.1.4/2; decomposition L3.15–L3.18.
#### Generality decision
`B` a Banach `K`-algebra with `NormOneClass` (needed for `algebraMap` to be contractive). Instances of use: `B = L` a complete extension field, `B` a Tate algebra.

### [CLEANUP-7] Run /cleanup on `TateAlgebra/Eval.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Eval.lean` · **Depends on**: T017, T018 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:19: DONE inline — Eval.lean sorry-free, runLinter clean, widths ≤ 100
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T019] The map of unit balls is local; evaluation preserves unit balls
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/EvalReduction.lean` · **Depends on**: CLEANUP-5, CLEANUP-7 · **Parallel**: no · **Type**: instance + lemma
- **Progress**: 2026-10-02T14:19: started · 2026-10-02T14:24: DONE — instance named isLocalHom_unitClosedBallMap; standard axioms
- **Leaves**: L4.1, L4.2

#### Statement
```lean
instance : IsLocalHom (unitClosedBallMap K L) := by sorry
theorem norm_aeval_le_one {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [NormOneClass B]
    [IsUltrametricDist B] [CompleteSpace B] {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    ‖aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ))‖ ≤ 1 := by sorry
```
#### Proof sketch
1. `IsLocalHom (unitClosedBallMap K L)`: `⟨fun a ha ↦ ?_⟩`; `rw [NormedRing.isUnit_iff_norm_eq_one] at ha ⊢`;
   `coe_unitClosedBallMap` and `norm_algebraMap'` turn `ha` into `‖(a : K)‖ = 1`.
2. `norm_aeval_le_one`: `(norm_aeval_le hx _).trans (Subring.norm_le_one f)`.
#### Mathlib lemmas needed
`norm_algebraMap'`. Chain: `NormedRing.isUnit_iff_norm_eq_one`, `Subring.norm_le_one`.
#### Sources
[BGR] 5.1.4, `bgr-5.1.md:257–266`; decomposition L4.1, L4.2.
#### Generality decision
`L` any normed field that is a normed `K`-algebra; `B` any Banach `K`-algebra in item 2.

### [T020] Reduction commutes with evaluation at a point
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/EvalReduction.lean` · **Depends on**: T019 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T14:24: DONE — private ringHom_ext_of_openUnitBall (vanish on T⁰⁰ + agree on K⁰[X]); added public reduction_C, reduction_X to Reduction.lean; coercions of ofUnitBallPolynomial need (K := K) (σ := σ) in show-steps; standard axioms
- **Leaves**: L4.3

#### Statement
```lean
theorem residue_aeval {x : σ → L} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    residue (unitClosedBall L)
        ⟨aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ)),
          mem_unitClosedBall.2 (norm_aeval_le_one hx f)⟩ =
      MvPolynomial.eval₂ (NormedField.residueFieldMap K L)
        (fun i ↦ residue (unitClosedBall L) ⟨x i, mem_unitClosedBall.2 (hx i)⟩) (reduction f) := by sorry
```
#### Proof sketch
Private lemma (shared with T021), for any ring `S`:
`ringHom_ext_of_openUnitBall {ψ₁ ψ₂ : unitClosedBall (Restricted K 1) →+* S}
  (h₁ : ∀ f ∈ openUnitBallIdeal _, ψ₁ f = 0) (h₂ : ∀ f ∈ openUnitBallIdeal _, ψ₂ f = 0)
  (h : ∀ p, ψ₁ (ofUnitBallPolynomial p) = ψ₂ (ofUnitBallPolynomial p)) : ψ₁ = ψ₂` —
for `f` take `p` from `exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal f` and write
`f = ofUnitBallPolynomial p + (f - ofUnitBallPolynomial p)`.

Then, with `ev : unitClosedBall (Restricted K 1) →+* unitClosedBall L` the restriction of `aeval 1 x hx`
(`RingHom.codRestrict` of `(aeval …).toRingHom.comp (unitClosedBall _).subtype`, membership by
`norm_aeval_le_one`):
1. `ψ₁ := (residue _).comp ev`, `ψ₂ := (MvPolynomial.eval₂Hom (residueFieldMap K L) x̃).comp reduction`,
   where `x̃ i := residue _ ⟨x i, _⟩`. The statement is `RingHom.congr_fun (… : ψ₁ = ψ₂) f` up to proof
   irrelevance in the subtype.
2. `h₁`: `‖aeval x f‖ ≤ ‖f‖ < 1`, so the residue is `0` (`residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`). `h₂`: `reduction_eq_zero_iff`.
3. `h`: both sides are ring homomorphisms in `p : MvPolynomial σ (unitClosedBall K)`; `MvPolynomial.ringHom_ext`.
   On `C a`: left is the residue of `algebraMap K L a` (`aeval_toRestricted`, `MvPolynomial.aeval_C`), which
   is `residueFieldMap K L (residue _ a)` by `IsLocalRing.ResidueField.map_residue`; right is the same by
   `reduction_ofUnitBallPolynomial`, `MvPolynomial.map_C`, `MvPolynomial.eval₂_C`. On `X i`: both are `x̃ i`.
#### Mathlib lemmas needed
`MvPolynomial.ringHom_ext`, `MvPolynomial.eval₂Hom`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X`, `MvPolynomial.map_C`, `MvPolynomial.map_X`, `IsLocalRing.ResidueField.map_residue`, `IsLocalRing.residue_eq_zero_iff`, `RingHom.codRestrict`.
#### Sources
[BGR] 5.1.4, `bgr-5.1.md:257–266`; [Bo] 1.2/5, `bosch-lectures.txt:449–456`; decomposition L4.3.
#### Generality decision
`L` any complete nonarchimedean normed extension field of `K` (BGR's `k_a` is not complete; see T025–T027). `K` need not be complete.

### [T021] Reduction commutes with substitution
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/EvalReduction.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T14:24: DONE — same argument with target MvPolynomial τ k; standard axioms
- **Leaves**: L4.4

#### Statement
```lean
theorem reduction_aeval {x : σ → Restricted K (1 : τ → ℝ)} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction ⟨aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ)),
        mem_unitClosedBall.2 (norm_aeval_le_one hx f)⟩ =
      MvPolynomial.aeval (fun i ↦ reduction ⟨x i, mem_unitClosedBall.2 (hx i)⟩) (reduction f) := by sorry
```
#### Proof sketch
The same argument with target `MvPolynomial τ k`:
`ψ₁ := reduction.comp ev` (`ev` the restriction of `aeval 1 x hx` to unit balls, into the unit ball of
`Restricted K (1 : τ → ℝ)`), `ψ₂ := (MvPolynomial.aeval fun i ↦ reduction ⟨x i, _⟩).toRingHom.comp reduction`.
1. Vanishing on the open unit ball: `norm_aeval_le` and `reduction_eq_zero_iff` on both sides.
2. On polynomials over `K⁰`, `MvPolynomial.ringHom_ext`. On `C a`: private lemma
   `reduction_C (a : unitClosedBall K) : reduction ⟨C 1 (a : K), _⟩ = MvPolynomial.C (residue _ a)`
   (`MvPolynomial.ext`, `coeff_reduction`, `val_C`, `MvPowerSeries.coeff_C`, `MvPolynomial.coeff_C`, split on
   `t = 0`); with `aeval_toRestricted`, `MvPolynomial.aeval_C`, `algebraMap_apply`. On `X i`: `aeval_X`,
   `MvPolynomial.aeval_X`.
#### Mathlib lemmas needed
`MvPolynomial.ringHom_ext`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X`, `MvPolynomial.coeff_C`, `MvPowerSeries.coeff_C`.
#### Sources
[BGR] `bgr-5.2.md:244` (`(σ(f))~ = σ̃(f̃)`); 5.1.3/7, `bgr-5.1.md:165–166`; decomposition L4.4.
#### Generality decision
`K` complete (the target Tate algebra must be complete). Source and target index types `σ`, `τ` independent.

### [CLEANUP-8] Run /cleanup on `TateAlgebra/EvalReduction.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/EvalReduction.lean` · **Depends on**: T021 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:24: DONE inline — EvalReduction sorry-free, runLinter clean, widths ≤ 100
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T022] Values at a point; kernels of points
- **Status**: done (2026-10-02) · **File**: `SupSeminorm.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T14:24: started · 2026-10-02T14:32: DONE — Ideal.Quotient.nontrivial_iff; range of φ is a field (Subalgebra.isField_of_algebraic) and quotientKerAlgEquivOfSurjective of rangeRestrict; dropped unused [Algebra.IsAlgebraic K L] from finite_quotient_ker (omit); standard axioms
- **Leaves**: L5.1–L5.4

#### Statement
```lean
theorem evalNorm_nonneg (x : MaximalSpectrum A) (f : A) : 0 ≤ evalNorm K x f := by sorry
theorem evalNorm_eq_zero_of_mem {x : MaximalSpectrum A} {f : A} (hf : f ∈ x.asIdeal) :
    evalNorm K x f = 0 := by sorry
theorem isMaximal_ker_of_isAlgebraic (φ : A →ₐ[K] L) : (RingHom.ker φ).IsMaximal := by sorry
theorem finite_quotient_ker [FiniteDimensional K L] (φ : A →ₐ[K] L) :
    Module.Finite K (A ⧸ RingHom.ker φ) := by sorry
```
#### Proof sketch
1. `evalNorm_nonneg`: `spectralValue_nonneg _`.
2. `evalNorm_eq_zero_of_mem`: `haveI := x.isMaximal`; `unfold evalNorm`;
   `rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, minpoly.zero]`; `X = X ^ 1` and `spectralValue_X_pow 1`.
3. `isMaximal_ker_of_isAlgebraic`: the quotient `A ⧸ RingHom.ker φ` is isomorphic to `φ.range`
   (`Ideal.quotientKerAlgEquivOfSurjective` for `φ.rangeRestrict`), and `φ.range` is a field by
   `Subalgebra.isField_of_algebraic`; transfer with `MulEquiv.isField` and conclude by
   `Ideal.Quotient.maximal_of_isField`.
4. `finite_quotient_ker`: `FiniteDimensional.of_injective (Ideal.kerLiftAlg φ).toLinearMap (Ideal.kerLiftAlg_injective φ)`.
#### Mathlib lemmas needed
`spectralValue_nonneg`, `Ideal.Quotient.eq_zero_iff_mem`, `minpoly.zero`, `spectralValue_X_pow`, `Subalgebra.isField_of_algebraic`, `Ideal.quotientKerAlgEquivOfSurjective`, `MulEquiv.isField`, `Ideal.Quotient.maximal_of_isField`, `Ideal.kerLiftAlg`, `Ideal.kerLiftAlg_injective`, `FiniteDimensional.of_injective`.
#### Sources
[BGR] 3.8.1/1–2, `bgr-3.8.md:18–35`; 5.1.4/6, `bgr-5.1.md:314–321`; `bgr-7.1.1.md:11–12`; decomposition L5.1–L5.4.
#### Generality decision
Items 1–2 for a normed field and any commutative `K`-algebra; items 3–4 for abstract fields (no norm). `φ` need not be surjective: an algebraic target makes the range a field.

### [T023] The value at the kernel of a point
- **Status**: done (2026-10-02) · **File**: `SupSeminorm.lean` · **Depends on**: T022 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T14:32: DONE — liftₐ injective, minpoly.algHom_eq, NormedAlgebra.norm_eq_spectralNorm, rfl; standard axioms
- **Leaves**: L5.5

#### Statement
```lean
theorem evalNorm_eq_norm_algHom (φ : A →ₐ[K] L) (x : MaximalSpectrum A)
    (hx : x.asIdeal = RingHom.ker φ) (f : A) : evalNorm K x f = ‖φ f‖ := by sorry
```
#### Proof sketch
1. `ψ : A ⧸ x.asIdeal →ₐ[K] L := Ideal.Quotient.liftₐ x.asIdeal φ fun a ha ↦ by rw [hx] at ha; exact ha`
   (`RingHom.mem_ker`), with `ψ (Ideal.Quotient.mk _ f) = φ f` (`Ideal.Quotient.liftₐ_apply` / `rfl`).
2. `ψ` is injective: `injective_iff_map_eq_zero`; a class `mk a` with `φ a = 0` has `a ∈ ker φ = x.asIdeal`
   (`Ideal.Quotient.mk_surjective` to pick representatives).
3. `unfold evalNorm`; `rw [← minpoly.algHom_eq ψ hψ]`; the left side is now
   `spectralValue (minpoly K (φ f)) = spectralNorm K L (φ f)` by definition, and
   `(NormedAlgebra.norm_eq_spectralNorm K (φ f)).symm` finishes.
#### Mathlib lemmas needed
`Ideal.Quotient.liftₐ`, `minpoly.algHom_eq`, `NormedAlgebra.norm_eq_spectralNorm`, `injective_iff_map_eq_zero`, `Ideal.Quotient.mk_surjective`.
#### Sources
[BGR] 5.1.4/6, `bgr-5.1.md:319–322`; decomposition L5.5.
#### Generality decision
`K` complete and nontrivially normed (the hypotheses of the Mathlib lemma: over a complete field the norm of an algebraic normed extension is the spectral norm). `L` need not be finite over `K`.

### [T024] `|f(x)| ≤ ‖f‖` in a Banach algebra
- **Status**: done (2026-10-02) · **File**: `SupSeminorm.lean` · **Depends on**: T022 · **Parallel**: no · **Type**: theorem + corollaries
- **Progress**: 2026-10-02T14:32: DONE — Bosch's unit argument with three private lemmas (coefficient bound σ^(r−n) from le_ciSup; spectralValue 0 = 0; σ^r = ‖q(0)‖ through AdjoinRoot q and spectralNorm_eq_norm_coeff_zero_rpow); Neumann unit times algebraMap of q(0); standard axioms
- **Leaves**: L5.6–L5.8

#### Statement
```lean
theorem evalNorm_le_norm (x : MaximalSpectrum A) (f : A) : evalNorm K x f ≤ ‖f‖ := by sorry
theorem bddAbove_range_evalNorm (f : A) :
    BddAbove (Set.range fun x : MaximalSpectrum A ↦ evalNorm K x f) := by sorry
theorem supSeminorm_le_norm (f : A) : supSeminorm K f ≤ ‖f‖ := by sorry
```
#### Proof sketch
`evalNorm_le_norm` (Bosch's unit argument). Let `y := Ideal.Quotient.mk x.asIdeal f`, `q := minpoly K y`,
`σ := spectralValue q`; `haveI := x.isMaximal`.
0. If `y` is not integral over `K`: `minpoly.eq_zero`, and `spectralValue 0 = 0` (unfold `spectralValue`,
   `spectralValueTerms`; every term is `0`), so the claim is `0 ≤ ‖f‖`.
1. Otherwise `q` is monic, irreducible (`minpoly.irreducible`; the quotient by a maximal ideal is a field),
   of degree `r ≥ 1` (`minpoly.natDegree_pos`). Suppose `‖f‖ < σ`.
2. `σ ^ r = ‖q.coeff 0‖`: in `AdjoinRoot q` (`Fact (Irreducible q)`), `minpoly K (AdjoinRoot.root q) = q`
   (`AdjoinRoot.minpoly_root`, `q` monic), so `σ = spectralNorm K (AdjoinRoot q) (root q)` and
   `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` gives `σ = ‖q.coeff 0‖ ^ (1 / r)`; raise to the `r`.
   In particular `q.coeff 0 ≠ 0`.
3. `‖q.coeff n‖ ≤ σ ^ (r - n)` for `n < r`: `le_ciSup (spectralValueTerms_bddAbove q) n` and
   `spectralValueTerms_of_lt_natDegree`, then raise to the power `r - n` (`Real.rpow_natCast`,
   `Real.rpow_mul`); for `n = r`, `‖1‖ = 1`.
4. `Polynomial.aeval f q = algebraMap K A (q.coeff 0) + w`, `w := ∑ n ∈ Finset.Icc 1 r, q.coeff n • f ^ n`
   (`Polynomial.aeval_eq_sum_range`, split off `n = 0`), and `‖w‖ < σ ^ r`: each term has norm
   `≤ σ ^ (r - n) * ‖f‖ ^ n < σ ^ r` (`norm_smul_le`, `norm_pow_le'`, `pow_lt_pow_left₀`), and a finite sum
   in an ultrametric group is bounded by a strict bound on its terms (take the maximum of finitely many
   terms: `IsUltrametricDist.exists_norm_finsetSum_le`).
5. `Polynomial.aeval f q` is a unit of `A`: it is `c • (1 - u)` with `c := q.coeff 0 ≠ 0`,
   `u := -(c⁻¹ • w)`, `‖u‖ < 1`; `isUnit_one_sub_of_norm_lt_one`.
6. But `Ideal.Quotient.mk _ (aeval f q) = aeval y q = 0` (`Polynomial.aeval_algHom_apply` for
   `Ideal.Quotient.mkₐ K _`, `minpoly.aeval`), so `aeval f q ∈ x.asIdeal`; `Ideal.eq_top_of_isUnit_mem`
   contradicts `x.isMaximal.ne_top`.

`bddAbove_range_evalNorm`: `⟨‖f‖, by rintro _ ⟨x, rfl⟩; exact evalNorm_le_norm x f⟩`.
`supSeminorm_le_norm`: `rcases isEmpty_or_nonempty (MaximalSpectrum A)`; `Real.iSup_of_isEmpty` and
`norm_nonneg`, or `ciSup_le fun x ↦ evalNorm_le_norm x f`.
#### Mathlib lemmas needed
`minpoly.eq_zero`, `minpoly.irreducible`, `minpoly.monic`, `minpoly.natDegree_pos`, `minpoly.aeval`, `AdjoinRoot.minpoly_root`, `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_bddAbove`, `le_ciSup`, `Polynomial.aeval_eq_sum_range`, `Polynomial.aeval_algHom_apply`, `IsUltrametricDist.exists_norm_finsetSum_le`, `norm_pow_le'`, `pow_lt_pow_left₀`, `isUnit_one_sub_of_norm_lt_one`, `Ideal.eq_top_of_isUnit_mem`, `Real.iSup_of_isEmpty`, `ciSup_le`.
#### Sources
[BGR] 3.8.2/1–2, `bgr-3.8.md:122–126`, `:147–152`; [Bo] 1.2/12, `bosch-lectures.txt:655–671`; decomposition L5.6–L5.8.
#### Generality decision
Any complete nonarchimedean Banach `K`-algebra; no `NormOneClass`, no power-multiplicativity, no normalisation of `‖f‖`. Steps 2–4 are worth three private lemmas.

### [CLEANUP-9] Run /cleanup on `SupSeminorm.lean`
- **Status**: done (2026-10-02) · **File**: `SupSeminorm.lean` · **Depends on**: T023, T024 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:32: DONE inline — SupSeminorm sorry-free, runLinter clean, widths ≤ 100, push_neg (deprecated) replaced by le_of_not_gt
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T025] Roots of unity with distinct residues
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/MaxModulus.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T14:32: started · 2026-10-02T14:40: DONE — roots of X^m−1 in the splitting field with the spectral normed-field structure; pairwise distance one by the geometric-sum identity G(s,s) − G(s,t) = (s−t)·W, ‖G(s,s)‖ = ‖m‖ = 1, ‖W‖ ≤ 1 (no derivative/multiset needed); added import Mathlib.Analysis.Normed.Ring.Ultra; standard axioms
- **Leaves**: L6.1, L6.2

#### Statement
```lean
theorem NormedField.exists_lt_natCast_norm_eq_one (K : Type*) [NormedField K]
    [IsUltrametricDist K] (d : ℕ) : ∃ m : ℕ, d < m ∧ ‖(m : K)‖ = 1 := by sorry
theorem exists_finset_splittingField_X_pow_sub_one {m : ℕ} (hm : 0 < m) (hmK : ‖(m : K)‖ = 1) :
    ∃ S : Finset (X ^ m - 1 : K[X]).SplittingField, S.card = m ∧
      (∀ s ∈ S, spectralNorm K _ s = 1) ∧
        ∀ s ∈ S, ∀ t ∈ S, s ≠ t → spectralNorm K _ (s - t) = 1 := by sorry
```
#### Proof sketch
1. `NormedField.exists_lt_natCast_norm_eq_one`: `by_cases h : ‖((d + 1 : ℕ) : K)‖ = 1`: take `m = d + 1`.
   Otherwise `‖((d + 1 : ℕ) : K)‖ < 1` (`IsUltrametricDist.norm_natCast_le_one`, `lt_of_le_of_ne`) and
   `m = d + 2`: `Nat.cast_succ`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` with `norm_one`,
   `max_eq_right`.
2. `exists_finset_splittingField_X_pow_sub_one`. Let `P : K[X] := X ^ m - 1`, `L := P.SplittingField`.
   - `(m : K) ≠ 0` from `hmK`; `P` separable: `Polynomial.separable_X_pow_sub_C 1 _ one_ne_zero`
     (`map_one`); `P` splits in `L`; so `Fintype.card (P.rootSet L) = m`
     (`Polynomial.card_rootSet_eq_natDegree`, `Polynomial.natDegree_X_pow_sub_C`). `S := (P.rootSet L).toFinset`.
   - `letI := spectralNorm.normedField K L; letI := spectralNorm.normedAlgebra K L`; now
     `‖z‖ = spectralNorm K L z` (`NormedAlgebra.norm_eq_spectralNorm K z`, or `rfl`), the norm is
     multiplicative and nonarchimedean (`isNonarchimedean_spectralNorm`).
   - For `s ∈ S`: `s ^ m = 1` (`Polynomial.mem_rootSet`, `aeval`), so `‖s‖ ^ m = 1` and `‖s‖ = 1`
     (`pow_eq_one_iff_of_nonneg`).
   - For `s ≠ t` in `S`: `Polynomial.Splits.eval_root_derivative` for `P.map (algebraMap K L)` at `s` gives
     `(m : L) * s ^ (m - 1) = ∏ over the other roots u of (s - u)`; the left side has norm `1`
     (`spectralNorm_extends`, `hmK`); every factor has norm `≤ max ‖s‖ ‖u‖ = 1`; a product of numbers in
     `[0, 1]` equal to `1` has every factor equal to `1` (if one were `< 1` the product would be `< 1`:
     `Finset.prod_le_prod` after isolating that factor).
#### Mathlib lemmas needed
`IsUltrametricDist.norm_natCast_le_one`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Polynomial.separable_X_pow_sub_C`, `Polynomial.SplittingField.splits`, `Polynomial.card_rootSet_eq_natDegree`, `Polynomial.natDegree_X_pow_sub_C`, `Polynomial.Splits.eval_root_derivative`, `Polynomial.derivative_X_pow`, `spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm_extends`, `isNonarchimedean_spectralNorm`, `isPowMul_spectralNorm` (there is no `spectralNorm_pow`).
#### Sources
[BGR] 5.1.4/3, `bgr-5.1.md:270–285` (the remark on extensions with large residue field); `bgr-3.2.md:76–79`; decomposition L6.1, L6.2, N6.
#### Generality decision
Item 1: any nonarchimedean normed field. Item 2: `K` complete and nontrivially normed (for the spectral normed-field structure), in `Type u` so that the splitting field is in the same universe. ⚠ Declared deviation: this replaces BGR's Lemma 3.4.1/4.

### [T026] Maximum modulus at the points of an extension field
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/MaxModulus.lean` · **Depends on**: CLEANUP-5, CLEANUP-8 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T14:40: DONE — residue map ρ injective on S; Nullstellensatz on the image; lift; residue_aeval + eval_map; scaling undone by map_smul/norm_smul; standard axioms
- **Leaves**: L6.3

#### Statement
```lean
theorem exists_norm_aeval_eq_norm (S : Finset L) (hS₁ : ∀ s ∈ S, ‖s‖ ≤ 1)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ‖s - t‖ = 1) (f : Restricted K (1 : σ → ℝ))
    (hf : ∀ t : σ →₀ ℕ, ‖coeff t f.1‖ = ‖f‖ → ∀ i, t i < S.card) :
    ∃ x : σ → L, ∃ hx : ∀ i, ‖x i‖ ≤ 1, (∀ i, x i ∈ S) ∧ ‖aeval (1 : σ → ℝ) x hx f‖ = ‖f‖ := by sorry
```
#### Proof sketch
0. `f = 0`: `rcases isEmpty_or_nonempty σ`. If `σ` is empty, `x := isEmptyElim`. Otherwise `hf 0 (by simp)`
   at any `i` gives `0 < S.card`, so pick `s ∈ S` and `x := fun _ ↦ s`; `map_zero`.
1. `f ≠ 0`: take `a ≠ 0` with `‖a • f‖ = 1` (`exists_norm_smul_eq_one`); `g : unitClosedBall _ := ⟨a • f, _⟩`.
   The indices `t` with `‖coeff t (a • f).1‖ = 1` are those with `‖coeff t f.1‖ = ‖f‖` (`norm_smul_eq`).
2. `q := reduction g ≠ 0` (`reduction_eq_zero_iff`); for `t ∈ q.support`, `‖coeff t g.1.1‖ = 1`, so `t i < S.card`
   by `hf`; hence `q.degreeOf i < S.card` (`MvPolynomial.degreeOf_lt_iff` / `degreeOf_le_iff`).
3. `Q := MvPolynomial.map (NormedField.residueFieldMap K L) q ≠ 0` (`MvPolynomial.map_injective`, a field
   homomorphism is injective) and `Q.degreeOf i ≤ q.degreeOf i` (`MvPolynomial.degrees_map_le`).
4. `S̃ := S.attach.image fun s ↦ residue _ ⟨s, _⟩` has `S.card` elements (`Finset.card_image_of_injOn`): for
   `s ≠ t`, `‖s - t‖ = 1` means `s - t ∉` the maximal ideal, so the residues differ.
5. `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ ↦ S̃)` contraposed: some `x̃` with `x̃ i ∈ S̃` has
   `MvPolynomial.eval x̃ Q ≠ 0`. Lift `x̃ i` to `x i ∈ S`.
6. `residue_aeval hx g` and `MvPolynomial.eval_map` give `residue ⟨aeval x (a • f), _⟩ = eval x̃ Q ≠ 0`, so
   `‖aeval x (a • f)‖ = 1` (not `< 1`, and `≤ 1` by `norm_aeval_le_one`). Undo the scaling: `map_smul`,
   `norm_smul`, `norm_smul_eq`.
#### Mathlib lemmas needed
`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`, `MvPolynomial.map_injective`, `MvPolynomial.degrees_map_le`, `MvPolynomial.degreeOf_le_iff`, `MvPolynomial.eval_map`, `Finset.card_image_of_injOn`, `IsLocalRing.residue_eq_zero_iff`, `RingHom.injective` (field).
#### Sources
[BGR] 5.1.4/3, `bgr-5.1.md:277–285`; [Bo] 1.2/5, `bosch-lectures.txt:442–456`; decomposition L6.3.
#### Generality decision
`K` any nonarchimedean normed field, `L` complete, `σ` finite (the Nullstellensatz lemma). The hypothesis on `S` is the exact count the proof uses, not BGR's "infinite".

### [T027] Maximum modulus on the maximal spectrum
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/MaxModulus.lean` · **Depends on**: T025, T026, CLEANUP-9 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T14:40: DONE — private evalNorm_mul_of_finite (spectralAlgNorm_mul on the residue field made a Field by Ideal.Quotient.field) and private exists_evalNorm_eq_norm_of_ne_zero (spot3 assembly); notMem via the product f*g; standard axioms
- **Leaves**: L6.4, L6.5

#### Statement
```lean
theorem exists_evalNorm_eq_norm (f : Restricted K (1 : σ → ℝ)) :
    ∃ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)),
      Module.Finite K (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal) ∧ evalNorm K x f = ‖f‖ := by sorry
theorem exists_evalNorm_eq_norm_and_notMem (f : Restricted K (1 : σ → ℝ))
    {g : Restricted K (1 : σ → ℝ)} (hg : g ≠ 0) :
    ∃ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)), evalNorm K x f = ‖f‖ ∧ g ∉ x.asIdeal := by sorry
```
#### Proof sketch
Private lemma `exists_point (f) (hf : f ≠ 0) : ∃ (L : Type u) (_ : NormedField L) (_ : NormedAlgebra K L)
(_ : IsUltrametricDist L) (_ : CompleteSpace L) (_ : FiniteDimensional K L) (x : σ → L) (hx : ∀ i, ‖x i‖ ≤ 1),
‖aeval 1 x hx f‖ = ‖f‖`:
- the set `{t | ‖coeff t f.1‖ = ‖f‖}` is finite (`finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)`); let `d`
  bound all `t i` on it (`Finset.sup`, `σ` finite);
- `m > d` with `‖(m : K)‖ = 1` and `S` from T025; `L := (X ^ m - 1 : K[X]).SplittingField` with
  `letI := spectralNorm.normedField K L`, `spectralNorm.normedAlgebra K L`,
  `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm`,
  `spectralNorm.completeSpace K L` (the block compiles: `scratch/spot3.lean`, item 4);
- `exists_norm_aeval_eq_norm S … f` (T026).

1. `exists_evalNorm_eq_norm`: for `f ≠ 0` take the point; `φ := aeval 1 x hx`;
   `x₀ := ⟨RingHom.ker φ, isMaximal_ker_of_isAlgebraic φ⟩`; `finite_quotient_ker φ`;
   `evalNorm_eq_norm_algHom φ x₀ rfl f`. For `f = 0` use the point of `1` and `evalNorm_eq_zero_of_mem`.
2. `exists_evalNorm_eq_norm_and_notMem`: for `f ≠ 0` apply the private lemma to `f * g ≠ 0` (domain):
   `‖φ f‖ * ‖φ g‖ = ‖f‖ * ‖g‖` (`map_mul`, `norm_mul` twice), with `‖φ f‖ ≤ ‖f‖`, `‖φ g‖ ≤ ‖g‖`
   (`norm_aeval_le`) and both right sides positive, so both are equalities; then `evalNorm x₀ g = ‖g‖ ≠ 0`
   and `g ∉ x₀` by `evalNorm_eq_zero_of_mem`. For `f = 0` apply item 1 to `g`.
#### Mathlib lemmas needed
`spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `spectralNorm.completeSpace`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `isNonarchimedean_spectralNorm`, `Polynomial.IsSplittingField.finiteDimensional`, `Algebra.IsAlgebraic.of_finite`, `Finset.sup`, `Finset.le_sup`.
#### Sources
[BGR] 5.1.4/6, `bgr-5.1.md:307–323`; 5.1.4/4, `bgr-5.1.md:289–293`; [RM] §0.1.3–§0.1.4; decomposition L6.4, L6.5.
#### Generality decision
`K : Type u` complete, nontrivially normed; `σ` finite. The residue field of the point is finite by construction (no Noether normalisation; erratum E4).

### [CLEANUP-ALL-1] Run /cleanup-all before milestone M1 (T028)
- **Status**: done (2026-10-02) · **Depends on**: T027, CLEANUP-2, CLEANUP-5, CLEANUP-7, CLEANUP-8, CLEANUP-9 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:40: DONE inline — Basic, Reduction, Eval, EvalReduction, SupSeminorm, MaxModulus: build clean, runLinter clean, widths ≤ 100, standard axioms
- Sweep before the milestone: `TateAlgebra/{Basic, Reduction, Eval, EvalReduction, MaxModulus}.lean` and `SupSeminorm.lean`. It is also the mid-file cleanup of `MaxModulus.lean` (three proof tickets done). Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T028] The Gauss norm is the supremum norm
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/MaxModulus.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorem (milestone M1) · **Milestone**: M1
- **Progress**: 2026-10-02T14:40: DONE — MILESTONE M1: supSeminorm_eq_norm and eq_zero_of_forall_mem; standard axioms
- **Leaves**: L6.6, L6.7

#### Statement
```lean
theorem supSeminorm_eq_norm (f : Restricted K (1 : σ → ℝ)) : supSeminorm K f = ‖f‖ := by sorry
theorem eq_zero_of_forall_mem {f : Restricted K (1 : σ → ℝ)}
    (hf : ∀ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)), f ∈ x.asIdeal) : f = 0 := by sorry
```
#### Proof sketch
1. `supSeminorm_eq_norm`: `le_antisymm (supSeminorm_le_norm f) ?_`; `obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f`;
   `hx ▸ le_ciSup (bddAbove_range_evalNorm f) x`. The Banach-algebra instances on `Restricted K 1` are the
   floor's (`NormedCommRing`, `IsUltrametricDist`, `CompleteSpace`) and T003's `NormedAlgebra`.
2. `eq_zero_of_forall_mem`: `obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f`;
   `norm_eq_zero.1 (hx ▸ evalNorm_eq_zero_of_mem K (hf x))`.
#### Mathlib lemmas needed
`le_ciSup`, `norm_eq_zero`.
#### Sources
[BGR] 5.1.4/5–6, `bgr-5.1.md:295–300`, `:307–311`; [RM] §0.1.4; decomposition L6.6, L6.7.
#### Generality decision
Milestone M1. Stated for `Restricted K (1 : σ → ℝ)` with `σ` finite, which covers `TateAlgebra K n`.

### [CLEANUP-10] Run /cleanup on `TateAlgebra/MaxModulus.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/MaxModulus.lean` · **Depends on**: T028 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:40: DONE inline — MaxModulus.lean sorry-free, runLinter clean
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T029] The coefficients in `X 0`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G2–G6) · **Type**: lemmas
- **Progress**: 2026-10-02T14:40: started · 2026-10-02T14:46: coeffX0_add/smul, norm_coeffX0_le, norm_le_iff_forall_norm_coeffX0_le, tendsto_norm_coeffX0 proved; std axioms.
- **Leaves**: L7.1–L7.5

#### Statement
```lean
theorem coeffX0_add (g h : TateAlgebra K (n + 1)) (ν : ℕ) :
    coeffX0 (g + h) ν = coeffX0 g ν + coeffX0 h ν := by sorry
theorem coeffX0_smul (a : K) (g : TateAlgebra K (n + 1)) (ν : ℕ) :
    coeffX0 (a • g) ν = a • coeffX0 g ν := by sorry
theorem norm_coeffX0_le (g : TateAlgebra K (n + 1)) (ν : ℕ) : ‖coeffX0 g ν‖ ≤ ‖g‖ := by sorry
theorem norm_le_iff_forall_norm_coeffX0_le {ε : ℝ} (g : TateAlgebra K (n + 1)) :
    ‖g‖ ≤ ε ↔ ∀ ν, ‖coeffX0 g ν‖ ≤ ε := by sorry
theorem tendsto_norm_coeffX0 (g : TateAlgebra K (n + 1)) :
    Tendsto (fun ν ↦ ‖coeffX0 g ν‖) atTop (𝓝 0) := by sorry
```
#### Proof sketch
The seam is crossed only through `coeff_coeffX0` (Tower):
`coeff t (coeffX0 g ν).1 = coeff (Finsupp.cons ν t) g.1`.
1. `coeffX0_add`, `coeffX0_smul`: `Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)`; `coeff_coeffX0` on each
   side; `val_add`, `map_add` (resp. `val_smul`, `MvPowerSeries.coeff_smul`).
2. `norm_coeffX0_le`: `(norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ ?_`; `coeff_coeffX0`; `norm_coeff_le g _`.
3. `norm_le_iff_forall_norm_coeffX0_le`: `→`: item 2 and transitivity. `←`:
   `(norm_le_iff_forall_norm_coeff_le g).2 fun t ↦ ?_`; rewrite `t` as
   `Finsupp.cons (t 0) (Finsupp.tail t)` (`Finsupp.cons_tail`), then `← coeff_coeffX0` and
   `(norm_coeff_le _ _).trans (h (t 0))`.
4. `tendsto_norm_coeffX0`: `Metric.tendsto_atTop`; for `ε > 0` the set `{t | ε ≤ ‖coeff t g.1‖}` is finite
   (`finite_setOf_le_norm_coeff`); let `N` be the supremum of `t 0` over it; for `ν > N` every coefficient of
   `coeffX0 g ν` has norm `< ε` (`coeff_coeffX0`, `Finsupp.cons_zero`), so `‖coeffX0 g ν‖ < ε` by
   `norm_lt_iff_forall_norm_coeff_lt`. Do **not** go through the floor's `(finSuccEquiv …).2`.
#### Mathlib lemmas needed
`MvPowerSeries.ext`, `MvPowerSeries.coeff_smul`, `Finsupp.cons_tail`, `Finsupp.cons_zero`, `Metric.tendsto_atTop`, `Finset.sup`, `Finset.le_sup`. Tower: `coeff_coeffX0`.
#### Sources
[BGR] 5.1.1, `bgr-5.1.md:24` (`Tₙ = Tₙ₋₁⟨Xₙ⟩`); `bgr-5.2.md:175`; decomposition L7.1–L7.5.
#### Generality decision
Any normed field; no completeness.

### [T030] Polynomials in `X 0` inside the Tate algebra
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T029 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:46: ofTail_injective/X/C, ofPolynomial_X, norm_ofPolynomial_le_iff, norm_ofTail proved; new public ofTail_apply (rfl) + private eq_cons_iff, single_zero_eq_cons, single_succ_eq_cons; std axioms.
- **Leaves**: L7.6–L7.11

#### Statement
```lean
theorem ofTail_injective : Function.Injective (ofTail K n) := by sorry
theorem ofPolynomial_X : ofPolynomial K n Polynomial.X = Restricted.X K (1 : Fin (n + 1) → ℝ) 0 := by sorry
theorem ofTail_X (i : Fin n) :
    ofTail K n (Restricted.X K (1 : Fin n → ℝ) i) = Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ := by sorry
theorem ofTail_C (a : K) :
    ofTail K n (Restricted.C (1 : Fin n → ℝ) a) = Restricted.C (1 : Fin (n + 1) → ℝ) a := by sorry
theorem norm_ofPolynomial_le_iff {ε : ℝ} (p : Polynomial (TateAlgebra K n)) :
    ‖ofPolynomial K n p‖ ≤ ε ↔ ∀ i, ‖p.coeff i‖ ≤ ε := by sorry
theorem norm_ofTail (f : TateAlgebra K n) : ‖ofTail K n f‖ = ‖f‖ := by sorry
```
#### Proof sketch
1. `ofTail_injective`: `ofPolynomial_injective.comp Polynomial.C_injective`.
2. `ofPolynomial_X`, `ofTail_X`, `ofTail_C`: `Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)`;
   `coeff_ofPolynomial` (Tower) on the left; `Polynomial.coeff_X`, `Polynomial.coeff_C` for the polynomial
   coefficient; `val_X`, `val_C`, `val_one`, `MvPowerSeries.coeff_X`, `coeff_C`, `coeff_one` on both sides. The
   index facts are: `t = Finsupp.single 0 1 ↔ t 0 = 1 ∧ Finsupp.tail t = 0`,
   `t = Finsupp.single i.succ 1 ↔ t 0 = 0 ∧ Finsupp.tail t = Finsupp.single i 1`,
   `t = 0 ↔ t 0 = 0 ∧ Finsupp.tail t = 0`; prove them once as private lemmas from `Finsupp.cons_tail`
   (`Finsupp.ext`, `Fin.cases`).
3. `norm_ofPolynomial_le_iff`: `(norm_le_iff_forall_norm_coeffX0_le _).trans` and
   `simp only [coeffX0_ofPolynomial]`.
4. `norm_ofTail`: `le_antisymm`; `≤` by item 3 with `Polynomial.coeff_C` (split on `i = 0`); `≥` by
   `norm_coeffX0_le (ofTail K n f) 0` and `coeffX0_ofPolynomial`, `Polynomial.coeff_C_zero`.
#### Mathlib lemmas needed
`Polynomial.C_injective`, `Polynomial.coeff_X`, `Polynomial.coeff_C`, `Polynomial.coeff_C_zero`, `MvPowerSeries.coeff_X`, `MvPowerSeries.coeff_C`, `Finsupp.cons_tail`, `Finsupp.tail_cons`, `Finsupp.cons_zero`. Tower: `coeff_ofPolynomial`, `coeffX0_ofPolynomial`, `ofPolynomial_injective`.
#### Sources
[BGR] 5.2.3/3, `bgr-5.2.md:144–147`, `:175`; decomposition L7.6–L7.11.
#### Generality decision
The three value lemmas are `@[simp]`. `n = 0` makes `ofTail_X` vacuous.

### [T031] Distinguished series: nonzero, scalars, order zero
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T029, CLEANUP-4 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:46: ne_zero_of_isMulDistinguishedX0, isMulDistinguishedX0_smul_iff, isMulDistinguishedX0_zero_iff proved via private norm_eq_norm_coeff_zero; std axioms.
- **Leaves**: L7.12–L7.14

#### Statement
```lean
theorem ne_zero_of_isMulDistinguishedX0 {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) : g ≠ 0 := by sorry
theorem isMulDistinguishedX0_smul_iff {a : K} (ha : a ≠ 0) {g : TateAlgebra K (n + 1)} {s : ℕ} :
    IsMulDistinguishedX0 (a • g) s ↔ IsMulDistinguishedX0 g s := by sorry
theorem isMulDistinguishedX0_zero_iff [CompleteSpace K] {g : TateAlgebra K (n + 1)} :
    IsMulDistinguishedX0 g 0 ↔ IsUnit g := by sorry
```
#### Proof sketch
All three go through `isMulDistinguishedX0_iff` (Tower).
1. `ne_zero_of_isMulDistinguishedX0`: `rintro rfl`; the first component says `coeffX0 0 s` is a unit; it is
   `0` (`Restricted.ext`, `coeff_coeffX0`, `val_zero`), contradicting `not_isUnit_zero`.
2. `isMulDistinguishedX0_smul_iff`: rewrite both sides; `coeffX0_smul`, `norm_smul_eq` (cancel `‖a‖ > 0`
   with `mul_lt_mul_left`, `mul_right_inj'`); for units, `a • h = C 1 a * h` (`Algebra.smul_def`,
   `algebraMap_apply`) and `IsUnit.mul_iff` with `C 1 a` a unit.
3. `isMulDistinguishedX0_zero_iff`: with `g₀ := coeffX0 g 0`, `coeff 0 g₀.1 = coeff 0 g.1`
   (`coeff_coeffX0`, `Finsupp.cons_zero_zero`).
   - `→`: `isUnit_iff_norm_coeff_lt` for `g₀` gives `coeff 0 ≠ 0` and dominance inside `g₀`, whence
     `‖g₀‖ = ‖coeff 0 g.1‖` (`exists_norm_coeff_eq`). For `t ≠ 0`: if `t 0 = 0`, `coeff t g.1` is a nonconstant
     coefficient of `g₀`; if `t 0 > 0`, `‖coeff t g.1‖ ≤ ‖coeffX0 g (t 0)‖ < ‖g₀‖`. Conclude by
     `isUnit_iff_norm_coeff_lt` for `g`.
   - `←`: from `isUnit_iff_norm_coeff_lt` for `g`: `g₀` is a unit (its constant coefficient dominates its
     other coefficients), `‖g₀‖ = ‖coeff 0 g.1‖ = ‖g‖`, and for `ν > 0` every coefficient of `coeffX0 g ν` is a
     coefficient of `g` at an index `≠ 0`, so `‖coeffX0 g ν‖ < ‖g₀‖` by `norm_lt_iff_forall_norm_coeff_lt`.
#### Mathlib lemmas needed
`not_isUnit_zero`, `IsUnit.mul_iff`, `Algebra.smul_def`, `mul_lt_mul_left`, `Finsupp.cons_zero_zero`, `Finsupp.cons_ne_zero_iff`. Tower: `isMulDistinguishedX0_iff`, `coeff_coeffX0`.
#### Sources
[BGR] 5.2.1/1, `bgr-5.2.md:29–33`, `:57`; [Bo] `bosch-lectures.txt:477–478`; decomposition L7.12–L7.14.
#### Generality decision
Completeness only in item 3 (both directions use the unit criterion).

### [CLEANUP-11] Run /cleanup on `TateAlgebra/Distinguished.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T031 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:48: runLinter clean; two statement lines wrapped to ≤ 100; simple API lemmas keep mathlib-style no-docstring convention as in Basic/Reduction/Eval.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T032] Distinguishedness is read off the reduction
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: CLEANUP-11 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:48: coeff_finSuccEquiv_reduction (ext + finSuccEquiv_coeff_coeff + Subtype.ext) and isMulDistinguishedX0_iff_reduction proved per sketch; std axioms.
- **Leaves**: L7.15, L7.16

#### Statement
```lean
theorem coeff_finSuccEquiv_reduction (g : unitClosedBall (TateAlgebra K (n + 1))) (ν : ℕ) :
    (MvPolynomial.finSuccEquiv _ n (reduction g)).coeff ν =
      reduction ⟨coeffX0 (g : TateAlgebra K (n + 1)) ν,
        mem_unitClosedBall.2 ((norm_coeffX0_le _ ν).trans (Subring.norm_le_one g))⟩ := by sorry
theorem isMulDistinguishedX0_iff_reduction [CompleteSpace K]
    {g : unitClosedBall (TateAlgebra K (n + 1))} (hg : ‖(g : TateAlgebra K (n + 1))‖ = 1)
    {s : ℕ} :
    IsMulDistinguishedX0 (g : TateAlgebra K (n + 1)) s ↔
      (MvPolynomial.finSuccEquiv _ n (reduction g)).natDegree = s ∧
        IsUnit (MvPolynomial.finSuccEquiv _ n (reduction g)).leadingCoeff := by sorry
```
#### Proof sketch
1. `coeff_finSuccEquiv_reduction`: `MvPolynomial.ext _ _ fun t ↦ ?_`;
   `MvPolynomial.finSuccEquiv_coeff_coeff`, `coeff_reduction` on both sides; the two elements of `K⁰` agree
   by `Subtype.ext` and `coeff_coeffX0`.
2. `isMulDistinguishedX0_iff_reduction`. Let `P := finSuccEquiv _ n (reduction g)` and
   `g_ν := ⟨coeffX0 g ν, _⟩ ∈ T⁰`, so `P.coeff ν = reduction g_ν` (item 1). Rewrite the left side with
   `isMulDistinguishedX0_iff` and `hg`.
   - `→`: `‖coeffX0 g s‖ = 1`, `coeffX0 g s` a unit, `‖coeffX0 g ν‖ < 1` for `ν > s`. Then `P.coeff ν = 0`
     for `ν > s` (`reduction_eq_zero_iff`), `P.coeff s` is a unit (`isUnit_coe_iff_isUnit_reduction`), in
     particular nonzero: `P.natDegree = s` (`Polynomial.natDegree_le_iff_coeff_eq_zero`, `le_natDegree_of_ne_zero`)
     and `P.leadingCoeff = P.coeff s`.
   - `←`: `P.leadingCoeff = P.coeff s = reduction g_s` is a unit, hence nonzero: `‖coeffX0 g s‖ = 1`
     (`norm_eq_one_of_reduction_ne_zero`), `coeffX0 g s` is a unit (`isUnit_coe_iff_isUnit_reduction`), and
     for `ν > s`, `P.coeff ν = 0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`) gives `‖coeffX0 g ν‖ < 1`.
#### Mathlib lemmas needed
`MvPolynomial.finSuccEquiv_coeff_coeff`, `Polynomial.natDegree_le_iff_coeff_eq_zero`, `Polynomial.le_natDegree_of_ne_zero`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.leadingCoeff`.
#### Sources
[BGR] 5.2.1, `bgr-5.2.md:35–38`; [Bo] 1.2/6, `bosch-lectures.txt:469–477`; decomposition L7.15, L7.16.
#### Generality decision
`‖g‖ = 1` and completeness are both necessary. "Unitary of degree `s`" is `natDegree = s ∧ IsUnit leadingCoeff`; the junk case (zero reduction) cannot occur and is false on both sides.

### [T033] Weierstrass polynomials
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T030 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T14:52: isWeierstrassPolynomial_iff, X_pow, of_mul_left/right, isMulDistinguishedX0 proved via private one_le_norm_ofPolynomial; std axioms.
- **Leaves**: L7.17–L7.21

#### Statement
```lean
theorem isWeierstrassPolynomial_iff {ω : Polynomial (TateAlgebra K n)} :
    IsWeierstrassPolynomial K n ω ↔ ω.Monic ∧ ∀ i, ‖ω.coeff i‖ ≤ 1 := by sorry
theorem isWeierstrassPolynomial_X_pow (s : ℕ) :
    IsWeierstrassPolynomial K n (Polynomial.X ^ s) := by sorry
theorem IsWeierstrassPolynomial.of_mul_left {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : ω₁.Monic) (h₂ : ω₂.Monic) (h : IsWeierstrassPolynomial K n (ω₁ * ω₂)) :
    IsWeierstrassPolynomial K n ω₁ := by sorry
theorem IsWeierstrassPolynomial.of_mul_right {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : ω₁.Monic) (h₂ : ω₂.Monic) (h : IsWeierstrassPolynomial K n (ω₁ * ω₂)) :
    IsWeierstrassPolynomial K n ω₂ := by sorry
theorem IsWeierstrassPolynomial.isMulDistinguishedX0 {ω : Polynomial (TateAlgebra K n)}
    (hω : IsWeierstrassPolynomial K n ω) :
    IsMulDistinguishedX0 (ofPolynomial K n ω) ω.natDegree := by sorry
```
#### Proof sketch
Private helper: `one_le_norm_ofPolynomial (h : ω.Monic) : 1 ≤ ‖ofPolynomial K n ω‖` — from
`norm_coeffX0_le (ofPolynomial K n ω) ω.natDegree`, `coeffX0_ofPolynomial`, `h.coeff_natDegree`, `norm_one`.
1. `isWeierstrassPolynomial_iff`: `→`: `⟨h.monic, (norm_ofPolynomial_le_iff ω).1 h.norm_eq_one.le⟩`. `←`:
   `⟨hm, le_antisymm ((norm_ofPolynomial_le_iff ω).2 hc) (helper hm)⟩`.
2. `isWeierstrassPolynomial_X_pow`: item 1, `Polynomial.monic_X_pow`, `Polynomial.coeff_X_pow` (split the
   `if`; `norm_one`, `norm_zero`).
3. `of_mul_left`, `of_mul_right`: `a := ‖ofPolynomial K n ω₁‖`, `b := ‖ofPolynomial K n ω₂‖`;
   `a * b = 1` (`map_mul`, `norm_mul`, `h.norm_eq_one`), `1 ≤ a`, `1 ≤ b` (helper); then `a = 1` because
   `a ≤ a * b` (`le_mul_of_one_le_right`), and symmetrically.
4. `IsWeierstrassPolynomial.isMulDistinguishedX0`: `isMulDistinguishedX0_iff.2 ⟨?_, ?_, ?_⟩` with
   `coeffX0_ofPolynomial`: the coefficient at `natDegree` is `1` (`isUnit_one`, `norm_one`, `hω.norm_eq_one`);
   later coefficients vanish (`Polynomial.coeff_eq_zero_of_natDegree_lt`, `norm_zero`, `zero_lt_one`).
#### Mathlib lemmas needed
`Polynomial.Monic.coeff_natDegree`, `Polynomial.monic_X_pow`, `Polynomial.coeff_X_pow`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `le_mul_of_one_le_right`, `norm_mul`.
#### Sources
[BGR] 5.2.3/1–2, `bgr-5.2.md:122–131`; 5.2.2/1, `bgr-5.2.md:96–99`; decomposition L7.17–L7.21.
#### Generality decision
BGR's definition (monic of Gauss norm one), **not** the roadmap's "non-leading coefficients of norm `< 1`" (erratum E1). `of_mul` (the pair) is already assembled in the skeleton. No completeness.

### [T034] Weierstrass preparation on Weierstrass polynomials
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T032, T033 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T14:52: exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 (weierstrassPreparation_exists + IsUnit.unit) and eq_of_mul_eq_mul via private natDegree_eq_of_eq_mul (reduction + finSuccEquiv + natDegree of a unit is 0) then weierstrassPreparation_omega_unique; std axioms.
- **Leaves**: L7.22, L7.23

#### Statement
```lean
theorem exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 [CompleteSpace K]
    {g : TateAlgebra K (n + 1)} {s : ℕ} (hg : IsMulDistinguishedX0 g s) :
    ∃ (ω : Polynomial (TateAlgebra K n)) (e : (TateAlgebra K (n + 1))ˣ),
      IsWeierstrassPolynomial K n ω ∧ ω.natDegree = s ∧ g = e * ofPolynomial K n ω := by sorry
theorem IsWeierstrassPolynomial.eq_of_mul_eq_mul [CompleteSpace K]
    {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : IsWeierstrassPolynomial K n ω₁) (h₂ : IsWeierstrassPolynomial K n ω₂)
    {e₁ e₂ : (TateAlgebra K (n + 1))ˣ}
    (h : (e₁ : TateAlgebra K (n + 1)) * ofPolynomial K n ω₁ = e₂ * ofPolynomial K n ω₂) :
    ω₁ = ω₂ := by sorry
```
#### Proof sketch
1. `exists_isWeierstrassPolynomial_of_isMulDistinguishedX0`:
   `obtain ⟨ω, e, hm, hd, hn, he, hge⟩ := weierstrassPreparation_exists hg`;
   `exact ⟨ω, he.unit, ⟨hm, hn⟩, Polynomial.natDegree_eq_of_degree_eq_some hd, by simpa using hge⟩`.
2. `IsWeierstrassPolynomial.eq_of_mul_eq_mul`. Put `u := e₁⁻¹ * e₂`, so
   `ofPolynomial K n ω₁ = u * ofPolynomial K n ω₂`, and `sᵢ := ωᵢ.natDegree`.
   - `s₁ = s₂`: `‖u‖ = 1` (`norm_mul`, both polynomials of norm one). In `T⁰`:
     `⟨ofPolynomial ω₁, _⟩ = ⟨u, _⟩ * ⟨ofPolynomial ω₂, _⟩`, so the reductions satisfy `r₁ = ũ * r₂` with `ũ`
     a unit (`isUnit_coe_iff_isUnit_reduction`). Apply `MvPolynomial.finSuccEquiv`: `P₁ = U * P₂`, `U` a unit
     of a polynomial ring over a domain, so `U.natDegree = 0` (`Polynomial.natDegree_eq_zero_of_isUnit`) and
     `P₁.natDegree = P₂.natDegree` (`Polynomial.natDegree_mul`). By T032 (`→`) applied to the distinguished
     series `ofPolynomial ωᵢ` (T033), `Pᵢ.natDegree = sᵢ`.
   - `weierstrassPreparation_omega_unique (h₁.isMulDistinguishedX0) h₁.monic _ isUnit_one (one_mul _).symm
     h₂.monic _ u.isUnit ‹_›`, the degree arguments from `Polynomial.degree_eq_natDegree` and `s₁ = s₂`.
   Alternative for the degree step: Euclidean division of `ω₁` by `ω₂` and the floor's
   `weierstrassDivision_polynomial_of_isMulDistinguishedX0`.
#### Mathlib lemmas needed
`Polynomial.natDegree_eq_of_degree_eq_some`, `Polynomial.degree_eq_natDegree`, `Polynomial.natDegree_mul`, `Polynomial.natDegree_eq_zero_of_isUnit`, `IsUnit.unit`. Tower: `weierstrassPreparation_exists`, `weierstrassPreparation_omega_unique`.
#### Sources
[BGR] 5.2.2/1, `bgr-5.2.md:96–116`, `:133–134`; [Bo] 1.2/9, `bosch-lectures.txt:584–605`; decomposition L7.22, L7.23.
#### Generality decision
`K` complete. Item 2 is stronger than BGR's uniqueness (the degrees are not assumed equal); the extra step is the reduction argument.

### [CLEANUP-12] Run /cleanup on `TateAlgebra/Distinguished.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Distinguished.lean` · **Depends on**: T034 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:52: Distinguished.lean sorry-free; runLinter clean; widths ≤ 100; std axioms on every declaration.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T035] Remainders modulo a Weierstrass polynomial
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Finiteness.lean` · **Depends on**: CLEANUP-12 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T14:58: existsUnique_remainder + bijective_quotientMap per sketch (modByMonic_add_div now takes no Monic hypothesis); std axioms.
- **Leaves**: L8.1, L8.2

#### Statement
```lean
theorem IsWeierstrassPolynomial.existsUnique_remainder (hω : IsWeierstrassPolynomial K n ω)
    (f : TateAlgebra K (n + 1)) :
    ∃! r : Polynomial (TateAlgebra K n),
      r.degree < ω.degree ∧ f - ofPolynomial K n r ∈ Ideal.span {ofPolynomial K n ω} := by sorry
theorem IsWeierstrassPolynomial.bijective_quotientMap (hω : IsWeierstrassPolynomial K n ω) :
    Function.Bijective
      (Ideal.quotientMap ((Ideal.span {ω}).map (ofPolynomial K n)) (ofPolynomial K n)
        Ideal.le_comap_map) := by sorry
```
#### Proof sketch
Let `g := ofPolynomial K n ω`, `s := ω.natDegree`, `hg := hω.isMulDistinguishedX0`, and
`ω.degree = s` (`Polynomial.degree_eq_natDegree hω.monic.ne_zero`).
1. `existsUnique_remainder`: existence — `obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists hg f`;
   `f - ofPolynomial K n r = q * g` gives membership (`Ideal.mem_span_singleton'`). Uniqueness — from
   `f - ofPolynomial K n rᵢ = qᵢ * g` rebuild `f = g * qᵢ + ofPolynomial K n rᵢ` and apply
   `weierstrassDivision_r_unique hg`.
2. `bijective_quotientMap`. Note `(Ideal.span {ω}).map (ofPolynomial K n) = Ideal.span {g}`
   (`Ideal.map_span`, `Set.image_singleton`).
   - Surjective: `Ideal.Quotient.mk_surjective` gives `f`; take its remainder `r`; the image of the class of
     `r` is the class of `ofPolynomial K n r`, equal to that of `f` (`Ideal.Quotient.eq`).
   - Injective: `injective_iff_map_eq_zero`; for a class `mk p` mapping to `0`, `ofPolynomial K n p ∈ span {g}`.
     Write `p = ω * (p /ₘ ω) + p %ₘ ω` (`Polynomial.modByMonic_add_div`), `r₀ := p %ₘ ω`,
     `r₀.degree < ω.degree` (`Polynomial.degree_modByMonic_lt`). Then `ofPolynomial K n r₀ ∈ span {g}`, so both
     `r₀` and `0` are remainders of `f := ofPolynomial K n r₀`; by item 1, `r₀ = 0`, hence `p ∈ span {ω}`.
#### Mathlib lemmas needed
`Ideal.mem_span_singleton'`, `Ideal.map_span`, `Set.image_singleton`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq`, `Ideal.Quotient.eq_zero_iff_mem`, `injective_iff_map_eq_zero`, `Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`, `Polynomial.degree_eq_natDegree`, `Ideal.quotientMap_mk`. Tower: `weierstrassDivision_exists`, `weierstrassDivision_r_unique`.
#### Sources
[BGR] 5.2.3/3, `bgr-5.2.md:137–140`, `:164–168`; [Bo] `bosch-lectures.txt:696–703`; decomposition L8.1, L8.2.
#### Generality decision
`bijective_quotientMap` is stated in the exact shape of axiom (2) of `IsRueckert`. The isometry part of BGR 5.2.3/3 is not needed in Layer 0 and is not stated.

### [T036] `Tₙ → T_{n+1} ⧸ (ω)` is finite, and injective in positive degree
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Finiteness.lean` · **Depends on**: T035 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T14:58: finite_mk_comp_ofTail via rw [← hI] (no quotEquivOfEq needed) + Monic.finite_quotient (import Mathlib.RingTheory.AdjoinRoot added) + quotientMap_comp_mk; injective_mk_comp_ofTail via remainder uniqueness; std axioms.
- **Leaves**: L8.3, L8.4

#### Statement
```lean
theorem IsWeierstrassPolynomial.finite_mk_comp_ofTail (hω : IsWeierstrassPolynomial K n ω) :
    ((Ideal.Quotient.mk (Ideal.span {ofPolynomial K n ω})).comp (ofTail K n)).Finite := by sorry
theorem IsWeierstrassPolynomial.injective_mk_comp_ofTail (hω : IsWeierstrassPolynomial K n ω)
    (hdeg : 0 < ω.natDegree) :
    Function.Injective
      ((Ideal.Quotient.mk (Ideal.span {ofPolynomial K n ω})).comp (ofTail K n)) := by sorry
```
#### Proof sketch
1. `finite_mk_comp_ofTail`: the map factors as
   `Tₙ →[C] Tₙ[X] →[mk] Tₙ[X] ⧸ span {ω} →[quotientMap] T_{n+1} ⧸ (span {ω}).map (ofPolynomial K n)
   →[Ideal.quotEquivOfEq] T_{n+1} ⧸ span {ofPolynomial K n ω}`. The first composite `mk ∘ C` is finite: it is
   the `algebraMap` of `Polynomial.Monic.finite_quotient hω.monic` (`RingHom.Finite` unfolds to
   `Module.Finite` for `toAlgebra`; use `RingHom.finite_algebraMap`). The last two are surjective
   (`bijective_quotientMap`, an equivalence), hence finite (`RingHom.Finite.of_surjective`). Compose with
   `RingHom.Finite.comp` and identify the composite with the statement's map by `RingHom.ext`
   (`Ideal.quotientMap_mk`, `Ideal.quotEquivOfEq_mk`, `ofTail`).
2. `injective_mk_comp_ofTail`: `injective_iff_map_eq_zero`; if `ofTail K n a ∈ span {ofPolynomial K n ω}`, then
   for `f := ofTail K n a = ofPolynomial K n (Polynomial.C a)` both `Polynomial.C a` (degree `≤ 0 < ω.degree`
   by `hdeg`, `Polynomial.degree_C_le`) and `0` are remainders; uniqueness gives `C a = 0`, so `a = 0`.
#### Mathlib lemmas needed
`Polynomial.Monic.finite_quotient`, `RingHom.finite_algebraMap`, `RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `Ideal.quotEquivOfEq`, `Ideal.quotEquivOfEq_mk`, `Ideal.quotientMap_mk`, `Polynomial.degree_C_le`, `Polynomial.C_eq_zero`.
#### Sources
[BGR] 5.2.3/4, `bgr-5.2.md:185–187`; decomposition L8.3, L8.4.
#### Generality decision
Injectivity needs `0 < ω.natDegree` (for `ω = 1` the target is the zero ring); BGR's "monomorphism" assumes it silently.

### [T037] The Weierstrass finiteness theorem
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Finiteness.lean` · **Depends on**: T036 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T14:58: finite_comp_ofTail via Quotient.lift + of_comp_finite; distinguished form via preparation; finite_compHom by explicit generators X0^i • m_j and span_induction. TRAP: mul_smul fails on TateAlgebra (SemigroupAction not synthesized through the Restricted seam) — use smul_smul. std axioms.
- **Leaves**: L8.5–L8.7

#### Statement
```lean
theorem IsWeierstrassPolynomial.finite_comp_ofTail (hω : IsWeierstrassPolynomial K n ω)
    {A : Type*} [CommRing A] (φ : TateAlgebra K (n + 1) →+* A) (hφ : φ.Finite)
    (h0 : φ (ofPolynomial K n ω) = 0) : (φ.comp (ofTail K n)).Finite := by sorry
theorem finite_mk_comp_ofTail_of_isMulDistinguishedX0 {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) :
    ((Ideal.Quotient.mk (Ideal.span {g})).comp (ofTail K n)).Finite := by sorry
theorem IsWeierstrassPolynomial.finite_compHom (hω : IsWeierstrassPolynomial K n ω)
    (M : Type*) [AddCommGroup M] [Module (TateAlgebra K (n + 1)) M]
    [Module.Finite (TateAlgebra K (n + 1)) M] (h : ∀ m : M, ofPolynomial K n ω • m = 0) :
    @Module.Finite (TateAlgebra K n) M _ _ (Module.compHom M (ofTail K n)) := by sorry
```
#### Proof sketch
1. `finite_comp_ofTail`: `φ̄ := Ideal.Quotient.lift (Ideal.span {ofPolynomial K n ω}) φ ?_` (the ideal is
   in the kernel by `h0`: `Ideal.span_le`/`Ideal.mem_span_singleton'`), `φ = φ̄.comp (Ideal.Quotient.mk _)`
   (`Ideal.Quotient.lift_comp_mk`). `φ̄` is finite by `RingHom.Finite.of_comp_finite`; the map of T036 is
   finite; `RingHom.Finite.comp`, and `φ.comp (ofTail K n) = φ̄.comp ((Ideal.Quotient.mk _).comp (ofTail K n))`
   by `RingHom.ext`.
2. `finite_mk_comp_ofTail_of_isMulDistinguishedX0`: `obtain ⟨ω, e, hω, -, hge⟩ := exists_isWeierstrassPolynomial…`;
   apply item 1 to `φ := Ideal.Quotient.mk (Ideal.span {g})` (finite: surjective) with
   `h0 : mk (ofPolynomial K n ω) = 0` because `ofPolynomial K n ω = e⁻¹ * g ∈ span {g}`.
3. `finite_compHom`: `letI := Module.compHom M (ofTail K n)`. From generators `m₁, …, m_k` of `M` over
   `T_{n+1}` (`Module.Finite.fg_top`), the finite family `X 0 ^ i • m_j` (`i < ω.natDegree`) spans `M` over
   `Tₙ`: for `f` and `m_j`, `f = ofPolynomial ω * q + ofPolynomial r` (division), `ofPolynomial ω • m_j = 0`
   by `h`, and `ofPolynomial r • m_j = ∑ i ∈ range s, ofTail (r.coeff i) • (X 0 ^ i • m_j)`
   (`Polynomial.as_sum_range'`, `map_sum`, `ofPolynomial_X`). Conclude with `Module.Finite.of_fg` /
   `Submodule.fg_def` over the image finset.
#### Mathlib lemmas needed
`Ideal.Quotient.lift`, `Ideal.Quotient.lift_comp_mk`, `RingHom.Finite.of_comp_finite`, `RingHom.Finite.comp`, `RingHom.Finite.of_surjective`, `Module.Finite.fg_top`, `Polynomial.as_sum_range'`, `Submodule.fg_def`.
#### Sources
[BGR] 5.2.3/4, `bgr-5.2.md:183–201`; [Bo] 1.2/10, `bosch-lectures.txt:618–626`; [RM] §0.2.2; decomposition L8.5–L8.7.
#### Generality decision
`A` is any commutative ring (BGR's Banach structure on `A` is not used). The module form is the roadmap's; explicit generators avoid a scalar-tower detour.

### [CLEANUP-13] Run /cleanup on `TateAlgebra/Finiteness.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Finiteness.lean` · **Depends on**: T037 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T14:58: Finiteness.lean sorry-free, runLinter clean, widths ≤ 100, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T038] The shear of a polynomial ring
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T15:04: shearAlgHom_comp_shearAlgHom (algHom_ext + Fin.cases + C_add), shear_X_zero/succ via change to shearAlgHom R e 1; std axioms.
- **Leaves**: L9.1–L9.3

#### Statement
```lean
theorem shearAlgHom_comp_shearAlgHom (e : Fin n → ℕ) {a b : R} (hab : a + b = 0) :
    (shearAlgHom R e a).comp (shearAlgHom R e b) = AlgHom.id R _ := by sorry
theorem shear_X_zero (e : Fin n → ℕ) : shear R e (X 0) = X 0 := by sorry
theorem shear_X_succ (e : Fin n → ℕ) (i : Fin n) :
    shear R e (X i.succ) = X i.succ + X 0 ^ e i := by sorry
```
#### Proof sketch
1. `shearAlgHom_comp_shearAlgHom`: `MvPolynomial.algHom_ext fun j ↦ ?_`; `Fin.cases` on `j`.
   `j = 0`: `AlgHom.comp_apply`, `shearAlgHom`, `MvPolynomial.aeval_X`, `Fin.cases_zero` twice. `j = i.succ`:
   `aeval_X`, `Fin.cases_succ`, then `map_add`, `map_mul`, `map_pow`, `MvPolynomial.aeval_C`
   (`algebraMap = C`), `aeval_X`; the result is `X i.succ + C a * X 0 ^ e i + C b * X 0 ^ e i`; collect with
   `← add_mul`, `← map_add`, `hab`, `map_zero`, `zero_mul`, `add_zero`.
2. `shear_X_zero`, `shear_X_succ`: the coercion of `AlgEquiv.ofAlgHom` is `shearAlgHom R e 1` (`rfl`);
   `MvPolynomial.aeval_X`, `Fin.cases_zero` / `Fin.cases_succ`, `map_one`, `one_mul`.
#### Mathlib lemmas needed
`MvPolynomial.algHom_ext`, `MvPolynomial.aeval_X`, `MvPolynomial.aeval_C`, `Fin.cases_zero`, `Fin.cases_succ`, `AlgEquiv.ofAlgHom`.
#### Sources
[BGR] 5.1.3, Example, `bgr-5.1.md:198–204`; decomposition L9.1–L9.3.
#### Generality decision
Any commutative ring and any exponents. The parametrised `shearAlgHom R e a` exists so that the inverse (`a = -1`) is the same definition.

### [T039] Degree and leading coefficient of a sheared monomial
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T038 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T15:04: sum_pow_mul_ne_of_lt via private eq_of_sum_pow_mul_eq (structural recursion, mod t); private finSuccEquiv_shear_monomial (Finsupp.prod_pow) + private C_X_add_X_pow_ne_zero; degree/leadingCoeff lemmas; std axioms. TRAP: bare add_comm rewrote n + 1 inside Fin (n+1) — give the left summand.
- **Leaves**: L9.4–L9.6

#### Statement
```lean
theorem sum_pow_mul_ne_of_lt {t : ℕ} {v w : Fin (n + 1) →₀ ℕ} (hv : ∀ i, v i < t)
    (hw : ∀ i, w i < t) (hvw : v ≠ w) :
    ∑ i : Fin (n + 1), t ^ i.val * v i ≠ ∑ i : Fin (n + 1), t ^ i.val * w i := by sorry
theorem degreeOf_zero_shear_monomial (e : Fin n → ℕ) (v : Fin (n + 1) →₀ ℕ) {a : k}
    (ha : a ≠ 0) :
    ((shear k e) (monomial v a)).degreeOf 0 = v 0 + ∑ i : Fin n, e i * v i.succ := by sorry
theorem leadingCoeff_finSuccEquiv_shear_monomial {e : Fin n → ℕ} (he : ∀ i, 0 < e i)
    (v : Fin (n + 1) →₀ ℕ) (a : k) :
    (finSuccEquiv k n ((shear k e) (monomial v a))).leadingCoeff = C a := by sorry
```
#### Proof sketch
1. `sum_pow_mul_ne_of_lt`: prove the contrapositive for functions by induction on `n`, generalising `v w`:
   `∀ v w : Fin (n + 1) → ℕ, (∀ i, v i < t) → (∀ i, w i < t) → ∑ i, t ^ i.val * v i = ∑ i, t ^ i.val * w i → v = w`.
   `Fin.sum_univ_succ` gives `v 0 + t * ∑ i : Fin n, t ^ i.val * v i.succ` (`pow_succ`, `Finset.mul_sum`);
   reducing modulo `t` (`Nat.add_mul_mod_self_left`, `Nat.mod_eq_of_lt`) gives `v 0 = w 0`; cancel
   (`Nat.eq_of_mul_eq_mul_left`, `0 < t` from `hv 0`) and apply the induction hypothesis to the tails;
   `Fin.cases` to conclude. Transfer to `Finsupp` with `DFunLike.ext`.
2. Private product formula, for `e : Fin n → ℕ`, `v`, `a : k`:
   `finSuccEquiv k n (shear k e (monomial v a)) =
     Polynomial.C (C a) * Polynomial.X ^ v 0 * ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i) ^ v i.succ`
   — `MvPolynomial.monomial_eq`, `Finsupp.prod_fintype`, `Fin.prod_univ_succ`, then `map_mul`, `map_prod`,
   `map_pow`, `shear_X_zero`, `shear_X_succ`, `AlgEquiv.commutes`, and `finSuccEquiv_X_zero`,
   `finSuccEquiv_X_succ`, `finSuccEquiv` on constants.
3. `degreeOf_zero_shear_monomial`: `← MvPolynomial.natDegree_finSuccEquiv`, the formula,
   `Polynomial.natDegree_mul`, `natDegree_C`, `natDegree_X_pow`, `Polynomial.natDegree_prod`, `natDegree_pow`,
   and `(C (X i) + X ^ e i).natDegree = e i` (`add_comm`, `Polynomial.natDegree_X_pow_add_C`). All factors are
   nonzero (`a ≠ 0`; `X ^ e + C b` is monic for `e > 0` and is `C (1 + X i) ≠ 0` for `e = 0`).
4. `leadingCoeff_finSuccEquiv_shear_monomial`: the formula, `Polynomial.leadingCoeff_mul`, `leadingCoeff_C`,
   `leadingCoeff_X_pow`, `Polynomial.leadingCoeff_prod`, `leadingCoeff_pow`,
   `Polynomial.leadingCoeff_X_pow_add_C (he i)`. (For `a = 0` both sides are `0`.)
#### Mathlib lemmas needed
`Fin.sum_univ_succ`, `Fin.prod_univ_succ`, `Nat.add_mul_mod_self_left`, `Nat.mod_eq_of_lt`, `Nat.eq_of_mul_eq_mul_left`, `MvPolynomial.monomial_eq`, `Finsupp.prod_fintype`, `MvPolynomial.finSuccEquiv_X_zero`, `MvPolynomial.finSuccEquiv_X_succ`, `MvPolynomial.natDegree_finSuccEquiv`, `Polynomial.natDegree_mul`, `Polynomial.natDegree_prod`, `Polynomial.natDegree_X_pow_add_C`, `Polynomial.leadingCoeff_mul`, `Polynomial.leadingCoeff_prod`, `Polynomial.leadingCoeff_X_pow_add_C`. (`Nat.ofDigits_inj_of_len_eq` is an alternative for item 1.)
#### Sources
[Bo] 1.2/7, `bosch-lectures.txt:505–527`; [BGR] 5.2.4/1, `bgr-5.2.md:242–254`; decomposition L9.4–L9.6.
#### Generality decision
Strict bound `v i < t` (Bosch), so that base-`t` expansions are unique. The leading-coefficient lemma needs `0 < e i` (defect D1); the degree lemma does not.

### [T040] The shear makes the leading coefficient a unit
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T039 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:04: isUnit_leadingCoeff_finSuccEquiv_shear per sketch (as_sum, exists_max_image, add_sum_erase, leadingCoeff_add_of_degree_lt'); std axioms.
- **Leaves**: L9.7

#### Statement
```lean
theorem isUnit_leadingCoeff_finSuccEquiv_shear {f : MvPolynomial (Fin (n + 1)) k} (hf : f ≠ 0)
    {t : ℕ} (ht : ∀ v ∈ f.support, ∀ i, v i < t) :
    IsUnit (finSuccEquiv k n (shear k (fun i : Fin n ↦ t ^ (i.val + 1)) f)).leadingCoeff := by sorry
```
#### Proof sketch
Let `e i := t ^ (i.val + 1)` (positive: `0 < t` since `f.support` is nonempty and `ht`), and
`D v := ∑ j : Fin (n + 1), t ^ j.val * v j`; by `Fin.sum_univ_succ`, `D v = v 0 + ∑ i, e i * v i.succ`
(`pow_zero`, `one_mul`, `mul_comm`), the degree of T039.
1. `f = ∑ v ∈ f.support, monomial v (f.coeff v)` (`MvPolynomial.as_sum`); apply `shear` and `finSuccEquiv`
   (`map_sum`): `P = ∑ v ∈ f.support, P_v`, `P_v.natDegree = D v` and `P_v.leadingCoeff = C (f.coeff v)`
   (T039; `f.coeff v ≠ 0` on the support).
2. `obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support D (MvPolynomial.support_nonempty.2 hf)`; for
   `v ≠ m` in the support, `D v < D m` (`hmax` and `sum_pow_mul_ne_of_lt`).
3. `Finset.sum_eq_add_sum_sdiff_singleton_of_mem` (or `Finset.add_sum_erase`): `P = P_m + R` with
   `R.degree < P_m.degree` (`Polynomial.degree_sum_le`, `Finset.sup_lt_iff`, `Polynomial.degree_eq_natDegree`);
   `Polynomial.leadingCoeff_add_of_degree_lt'` (the form for the larger summand first) gives
   `P.leadingCoeff = C (f.coeff m)`, a unit (`IsUnit.map`, `isUnit_iff_ne_zero`).
#### Mathlib lemmas needed
`MvPolynomial.as_sum`, `MvPolynomial.support_nonempty`, `Finset.exists_max_image`, `Finset.add_sum_erase`, `Polynomial.degree_sum_le`, `Polynomial.leadingCoeff_add_of_degree_lt`, `Polynomial.leadingCoeff_add_of_degree_lt'`, `IsUnit.map`, `isUnit_iff_ne_zero`.
#### Sources
[Bo] 1.2/7, `bosch-lectures.txt:498–528`; [BGR] 5.2.4/1, `bgr-5.2.md:249–254`; decomposition L9.7.
#### Generality decision
A field `k` (the residue field). `n = 0` is the statement that a nonzero one-variable polynomial has a unit leading coefficient.

### [CLEANUP-14] Run /cleanup on `TateAlgebra/Chart.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T040 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:04: Chart.lean (polynomial half) runLinter clean, widths ≤ 100; remaining sorries are T041–T043 only.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T041] The shear of the Tate algebra is an isometric automorphism
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: CLEANUP-14, CLEANUP-7 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T15:10: norm_shearTuple_le_one, shearAlgHom_comp_shearAlgHom (continuity stated separately: inline .comp unification timed out at whnf), shear_X_zero/succ, norm_shear (two-sided contraction); new public simp lemmas shearTuple_zero/shearTuple_succ (rfl); std axioms.
- **Leaves**: L9.8–L9.12

#### Statement
```lean
omit [CompleteSpace K] in
theorem norm_shearTuple_le_one (e : Fin n → ℕ) {a : K} (ha : ‖a‖ ≤ 1) (i : Fin (n + 1)) :
    ‖shearTuple K n e a i‖ ≤ 1 := by sorry
theorem shearAlgHom_comp_shearAlgHom (e : Fin n → ℕ) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : a + b = 0) :
    (shearAlgHom K n e a ha).comp (shearAlgHom K n e b hb) = AlgHom.id K _ := by sorry
theorem shear_X_zero (e : Fin n → ℕ) :
    shear K n e (Restricted.X K (1 : Fin (n + 1) → ℝ) 0) =
      Restricted.X K (1 : Fin (n + 1) → ℝ) 0 := by sorry
theorem shear_X_succ (e : Fin n → ℕ) (i : Fin n) :
    shear K n e (Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ) =
      Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ +
        Restricted.X K (1 : Fin (n + 1) → ℝ) 0 ^ e i := by sorry
theorem norm_shear (e : Fin n → ℕ) (f : TateAlgebra K (n + 1)) : ‖shear K n e f‖ = ‖f‖ := by sorry
```
#### Proof sketch
1. `norm_shearTuple_le_one`: `Fin.cases` on `i`. `0`: `Restricted.norm_X`, `norm_one`, `mul_one`. `succ`:
   `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)`; the first is `norm_X`; the second
   `norm_mul_le`, `norm_C`, `norm_pow_le`, `norm_X`, `one_pow`, `mul_one`, `ha`.
2. `shearAlgHom_comp_shearAlgHom`: `algHom_ext_of_continuous ?_ continuous_id fun j ↦ ?_` (T017); continuity
   of the composite from `continuous_aeval` twice (T018); on `X j`: `AlgHom.comp_apply`, `aeval_X`, `Fin.cases`
   on `j`, and for a successor `map_add`, `map_mul`, `map_pow`, `aeval_X`, with
   `Restricted.C 1 b = algebraMap K _ b` (`algebraMap_apply`) and `AlgHom.commutes`; collect as in T038.
3. `shear_X_zero`, `shear_X_succ`: the coercion of `AlgEquiv.ofAlgHom` is `aeval 1 (shearTuple K n e 1) _`;
   `aeval_X`, `shearTuple`, `Fin.cases_zero` / `Fin.cases_succ`, `map_one`, `one_mul`.
4. `norm_shear`: `le_antisymm (norm_aeval_le _ f) ?_`; `calc ‖f‖ = ‖(shear K n e).symm (shear K n e f)‖`
   (`AlgEquiv.symm_apply_apply`) `≤ ‖shear K n e f‖` (`norm_aeval_le`, the inverse being
   `aeval 1 (shearTuple K n e (-1)) _`).
#### Mathlib lemmas needed
`IsUltrametricDist.norm_add_le_max`, `norm_mul_le`, `norm_pow_le`, `AlgHom.comp_apply`, `AlgHom.commutes`, `AlgEquiv.symm_apply_apply`, `continuous_id`. Floor: `Restricted.norm_X`, `Restricted.norm_C`, `Restricted.algebraMap_apply`.
#### Sources
[BGR] 5.1.3, Example, `bgr-5.1.md:198–204`; [Bo] 1.2/7, `bosch-lectures.txt:488–497`; decomposition L9.8–L9.12.
#### Generality decision
`K` complete (substitution into a complete algebra). The isometry is Bosch's two-sided contraction; BGR's 5.1.3/4 is not needed.

### [T042] The reduction of the shear is the shear of the reduction
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T041, CLEANUP-8 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:10: reduction_shear via reduction_aeval + congr 2 + funext/Fin.cases; std axioms.
- **Leaves**: L9.13

#### Statement
```lean
theorem reduction_shear (e : Fin n → ℕ) (f : unitClosedBall (TateAlgebra K (n + 1))) :
    reduction ⟨shear K n e (f : TateAlgebra K (n + 1)),
        mem_unitClosedBall.2 ((norm_shear e _).trans_le (Subring.norm_le_one f))⟩ =
      MvPolynomial.shear _ e (reduction f) := by sorry
```
#### Proof sketch
Private lemma `reduction_X (i) : reduction ⟨Restricted.X K 1 i, _⟩ = MvPolynomial.X i` — `MvPolynomial.ext`,
`coeff_reduction`, `val_X`, `MvPowerSeries.coeff_X`, `MvPolynomial.coeff_X`; the residue of `1` is `1` and
of `0` is `0` (split the `if`).

Then `reduction_aeval (x := shearTuple K n e 1) _ f` (T021) gives
`reduction ⟨shear K n e f, _⟩ = MvPolynomial.aeval (fun i ↦ reduction ⟨shearTuple K n e 1 i, _⟩) (reduction f)`
(the two membership proofs agree by proof irrelevance; `shear K n e f` unfolds to the `aeval` by `rfl`), and
`MvPolynomial.shear _ e = aeval (Fin.cases (X 0) fun i ↦ X i.succ + C 1 * X 0 ^ e i)`. So it remains to show
the two tuples are equal: `funext`, `Fin.cases`. At `0`: `reduction_X`. At `i.succ`: the element of `T⁰` is
`⟨X i.succ, _⟩ + ⟨C 1 1, _⟩ * ⟨X 0, _⟩ ^ e i` (`Subtype.ext`), so `map_add`, `map_mul`, `map_pow`,
`reduction_X`, and the reduction of `C 1 1 = 1` is `1 = C 1`.
#### Mathlib lemmas needed
`MvPolynomial.coeff_X`, `MvPowerSeries.coeff_X`, `MvPolynomial.ext`, `Fin.cases_zero`, `Fin.cases_succ`.
#### Sources
[BGR] 5.2.4/1, `bgr-5.2.md:244`; decomposition L9.13.
#### Generality decision
Stated for the unit ball element `⟨shear K n e f, _⟩` with the membership proof spelled in the statement.

### [T043] Distinguished charts
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T040, T042, CLEANUP-12 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:10: exists_isMulDistinguishedX0_shear per sketch (coefficient norms via simp only [val_smul, coeff_smul] — rw across the seam failed; generalise the order before rw [map_smul]); private exists_bound_of_ne_zero; exists_shear_forall via choose! + Finset.le_sup; std axioms.
- **Leaves**: L9.14–L9.16

#### Statement
```lean
theorem exists_isMulDistinguishedX0_shear {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) {t : ℕ}
    (ht : ∀ ν : Fin (n + 1) →₀ ℕ, ‖MvPowerSeries.coeff ν f.1‖ = ‖f‖ → ∀ i, ν i < t) :
    ∃ s, IsMulDistinguishedX0 (shear K n (fun i : Fin n ↦ t ^ (i.val + 1)) f) s := by sorry
theorem exists_shear_isMulDistinguishedX0 {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) :
    ∃ (e : Fin n → ℕ) (s : ℕ), IsMulDistinguishedX0 (shear K n e f) s := by sorry
theorem exists_shear_forall_isMulDistinguishedX0 (F : Finset (TateAlgebra K (n + 1)))
    (hF : ∀ f ∈ F, f ≠ 0) :
    ∃ e : Fin n → ℕ, ∀ f ∈ F, ∃ s, IsMulDistinguishedX0 (shear K n e f) s := by sorry
```
#### Proof sketch
1. `exists_isMulDistinguishedX0_shear`. Let `e i := t ^ (i.val + 1)`, `σ := shear K n e`.
   - Take `a ≠ 0` with `‖a • f‖ = 1`; `g : unitClosedBall _ := ⟨a • f, _⟩`; `q := reduction g ≠ 0`.
   - For `v ∈ q.support`: `‖coeff v (a • f).1‖ = 1`, so `‖coeff v f.1‖ = ‖f‖` (`norm_smul_eq`,
     `MvPowerSeries.coeff_smul`) and `ht` gives `v i < t`.
   - `isUnit_leadingCoeff_finSuccEquiv_shear` (T040) for `q`; `reduction_shear e g` (T042) rewrites the
     reduction of `σ (a • f)`; `norm_shear` gives `‖σ (a • f)‖ = 1`.
   - `isMulDistinguishedX0_iff_reduction` (`←`) with `s := (finSuccEquiv _ n (shear _ e q)).natDegree`.
   - `σ (a • f) = a • σ f` (`map_smul`) and `isMulDistinguishedX0_smul_iff ha`.
2. `exists_shear_isMulDistinguishedX0`: `hfin := finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)`;
   `t := (hfin.toFinset.sup fun ν ↦ Finset.univ.sup fun i ↦ ν i) + 1`; an index with `‖coeff ν f.1‖ = ‖f‖`
   lies in `hfin.toFinset`, so `ν i < t` (`Finset.le_sup`, `Nat.lt_succ_of_le`); item 1.
3. `exists_shear_forall_isMulDistinguishedX0`: the same with `t` the maximum of the bounds over `f ∈ F`
   (`Finset.sup` over `F.attach`, or induction on `F` with `max`); item 1 for each `f`.
#### Mathlib lemmas needed
`MvPowerSeries.coeff_smul`, `map_smul`, `Finset.sup`, `Finset.le_sup`, `Set.Finite.toFinset`, `Nat.lt_succ_of_le`, `norm_pos_iff`.
#### Sources
[BGR] 5.2.4/1–2, `bgr-5.2.md:219–264`; [Bo] 1.2/7, `bosch-lectures.txt:479–531`; decomposition L9.14–L9.16.
#### Generality decision
`t` strictly exceeds the exponents of the coefficients of maximal norm, exponents `t ^ (i + 1)`: Bosch's convention, equal to BGR's `(1 + t)^j` after the shift. The relative form of Bosch 1.8/13 is not here (erratum E8).

### [CLEANUP-15] Run /cleanup on `TateAlgebra/Chart.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Chart.lean` · **Depends on**: T043 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:10: Chart.lean sorry-free, runLinter clean, widths ≤ 100, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T044] Two facts about the Krull dimension
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T15:16: ringKrullDim_le_of_isIntegral (krullDim_le_of_strictMono + comap_lt_comap_of_integral_mem_sdiff) and ringKrullDim_le_add_one_of_forall_quotient_le (krullDim_eq_iSup_coheight + coheight_eq_iSup_gt_coheight + coheight_eq_krullDim_Ici + ringKrullDim_quotient); add_le_add_right now adds on the left — use add_le_add h le_rfl; std axioms.
- **Leaves**: L10.1, L10.2

#### Statement
```lean
theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by sorry
theorem ringKrullDim_le_add_one_of_forall_quotient_le {R : Type*} [CommRing R] {d : WithBot ℕ∞}
    (hd : 0 ≤ d)
    (h : ∀ p q : Ideal R, p.IsPrime → q.IsPrime → q < p → ringKrullDim (R ⧸ p) ≤ d) :
    ringKrullDim R ≤ d + 1 := by sorry
```
#### Proof sketch
1. `ringKrullDim_le_of_isIntegral`: `algebraize [f]` (or `letI := f.toAlgebra`); then
   `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun p q hpq ↦ ?_`. From
   `hpq : p < q`: `p.asIdeal ≤ q.asIdeal` and some `x ∈ q.asIdeal`, `x ∉ p.asIdeal`
   (`SetLike.exists_of_lt`); `Ideal.comap_lt_comap_of_integral_mem_sdiff hpq.le ⟨hx, hx'⟩ (hf x)` is the
   strict inequality of the contractions (unfold `RingHom.IsIntegral` to `IsIntegral R x`).
2. `ringKrullDim_le_add_one_of_forall_quotient_le`: `ringKrullDim R = Order.krullDim (PrimeSpectrum R)` is
   `⨆ p : LTSeries _, p.length`; `iSup_le fun p ↦ ?_`. Case `p.length = 0`: `0 ≤ d + 1` from `hd`. Case
   `p.length = ℓ + 1`: `x := p 1` (`⟨1, by omega⟩ : Fin (p.length + 1)`), `p 0 < p 1` (`p.strictMono`).
   `Order.rev_index_le_coheight p 1` gives `ℓ ≤ coheight x`; `Order.coheight_eq_krullDim_Ici x` turns it into
   `ℓ ≤ krullDim (Set.Ici x)`; `Set.Ici x = PrimeSpectrum.zeroLocus x.asIdeal` (`Set.ext`,
   `PrimeSpectrum.mem_zeroLocus`, `PrimeSpectrum.asIdeal_le_asIdeal`), and `ringKrullDim_quotient` identifies
   that with `ringKrullDim (R ⧸ x.asIdeal) ≤ d` (`h` with `q := (p 0).asIdeal`). Finish in `WithBot ℕ∞`:
   `Nat.cast_add_one`-style casts and `add_le_add_right`.
#### Mathlib lemmas needed
`Order.krullDim_le_of_strictMono`, `PrimeSpectrum.comap`, `Ideal.comap_lt_comap_of_integral_mem_sdiff`, `Order.rev_index_le_coheight`, `Order.coheight_eq_krullDim_Ici`, `ringKrullDim_quotient`, `PrimeSpectrum.mem_zeroLocus`, `LTSeries.strictMono`. (There is no `Order.krullDim_le_iff` and no Mathlib lemma for integral maps.)
#### Sources
[BGR] 6.1.2, Remark, `bgr-6.1.2.md:49–57` (Nagata 10.10; chains of primes); [Bo] `bosch-lectures.txt:631–632`; decomposition L10.1, L10.2.
#### Generality decision
Item 1 needs no injectivity. Item 2 needs `0 ≤ d` (a field has dimension `0` and no pair `q < p`).

### [T045] Rückert overrings: the noetherian property
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: T044 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:16: finite_mk_comp_C, exists_ringEquiv_mem_map, isNoetherianRing per sketch (fg_of_fg_map_of_fg_inf_ker_of_surjective needs f := mk J explicit); import Mathlib.RingTheory.AdjoinRoot added; std axioms.
- **Leaves**: L10.3–L10.5

#### Statement
```lean
theorem finite_mk_comp_C (h : IsRueckert φ W) {ω : I[X]} (hω : ω ∈ W) :
    ((Ideal.Quotient.mk ((Ideal.span {ω}).map φ)).comp (φ.comp C)).Finite := by sorry
theorem exists_ringEquiv_mem_map (h : IsRueckert φ W) {a : Ideal I'} (ha : a ≠ ⊥) :
    ∃ (σ : I' ≃+* I') (ω : I[X]), ω ∈ W ∧ φ ω ∈ a.map (σ : I' →+* I') := by sorry
theorem isNoetherianRing (h : IsRueckert φ W) [IsNoetherianRing I] : IsNoetherianRing I' := by sorry
```
#### Proof sketch
1. `finite_mk_comp_C`: `(Ideal.Quotient.mk (span {ω})).comp C` is finite
   (`Polynomial.Monic.finite_quotient (h.monic ω hω)` through `RingHom.finite_algebraMap`); the quotient map
   of axiom (2) is surjective, hence finite; `RingHom.Finite.comp`; the composite is the statement's map by
   `Ideal.quotientMap_comp_mk` (`RingHom.comp_assoc`).
2. `exists_ringEquiv_mem_map`: `obtain ⟨f, hfa, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha`;
   `obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf0`; `⟨σ, ω, hω, he ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hfa)⟩`.
3. `isNoetherianRing`: `(isNoetherianRing_iff_ideal_fg _).2 fun a ↦ ?_`; `a = ⊥` is finitely generated.
   Otherwise take `σ`, `ω` from item 2, `J := (Ideal.span {ω}).map φ`, `a' := a.map (σ : I' →+* I')`.
   - `I' ⧸ J` is noetherian: `isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _ (h.bijective_quotientMap ω hω))`
     from `Ideal.Quotient.isNoetherianRing` and `Polynomial.isNoetherianRing`.
   - `a'.FG`: `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective (f := Ideal.Quotient.mk J) ?_ ?_ Ideal.Quotient.mk_surjective`;
     the image is finitely generated (noetherian ring); `a' ⊓ RingHom.ker (mk J) = J` (`Ideal.mk_ker`,
     `inf_eq_right`, `J ≤ a'` from `φ ω ∈ a'` and `Ideal.map_span`), finitely generated by one element.
   - back to `a`: `a = a'.map σ.symm` (`Ideal.map_of_equiv`) and `Ideal.FG.map`.
#### Mathlib lemmas needed
`Polynomial.Monic.finite_quotient`, `RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `Ideal.quotientMap_comp_mk`, `Submodule.exists_mem_ne_zero_of_ne_bot`, `Ideal.mem_map_of_mem`, `isNoetherianRing_iff_ideal_fg`, `Polynomial.isNoetherianRing`, `Ideal.Quotient.isNoetherianRing`, `RingEquiv.ofBijective`, `isNoetherianRing_of_ringEquiv`, `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective`, `Ideal.mk_ker`, `Ideal.map_of_equiv`, `Ideal.FG.map`, `Ideal.map_span`.
#### Sources
[BGR] 5.2.5/1–2, `bgr-5.2.md:272–297`; decomposition L10.3–L10.5.
#### Generality decision
Abstract `IsRueckert φ W` for commutative rings; injectivity of `φ` is not used here.

### [T046] Rückert overrings: the Jacobson property
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: T045 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:16: private jacobson_eq_self_of_isPrime (integral I → I'/p' via factor ∘ mk ∘ φ ∘ C, isJacobsonRing_of_isIntegral', jacobson_eq_iff_jacobson_quotient_eq_bot), jacobson_eq_radical, isJacobsonRing; Ideal.bot_prime deprecated → Ideal.isPrime_bot; std axioms.
- **Leaves**: L10.6, L10.7

#### Statement
```lean
theorem jacobson_eq_radical (h : IsRueckert φ W) [IsJacobsonRing I] {a : Ideal I'} (ha : a ≠ ⊥) :
    a.jacobson = a.radical := by sorry
theorem isJacobsonRing (h : IsRueckert φ W) [IsJacobsonRing I]
    (h0 : (⊥ : Ideal I').jacobson = ⊥) : IsJacobsonRing I' := by sorry
```
#### Proof sketch
1. `jacobson_eq_radical`: `le_antisymm ?_ Ideal.radical_le_jacobson`. `rw [Ideal.radical_eq_sInf]`;
   `le_sInf fun p ⟨hap, hp⟩ ↦ ?_`; it suffices that `p.jacobson = p` (then `Ideal.jacobson_mono hap`). The
   prime `p` is nonzero (`a ≠ ⊥`, `a ≤ p`).
   Private lemma `jacobson_eq_self_of_isPrime (h : IsRueckert φ W) [IsJacobsonRing I] {p : Ideal I'}
   [p.IsPrime] (hp : p ≠ ⊥) : p.jacobson = p`:
   - `obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map hp`; `p' := p.map σ` is prime
     (`Ideal.map_isPrime_of_equiv`) and it suffices to treat `p'`
     (`Ideal.map_jacobson_of_bijective σ.bijective`, `Ideal.map_of_equiv`).
   - `J := (Ideal.span {ω}).map φ ≤ p'`. The map `I → I' ⧸ p'` is
     `(Ideal.Quotient.factor _).comp ((Ideal.Quotient.mk J).comp (φ.comp C))`: integral, as a finite map
     (`h.finite_mk_comp_C hω`, `RingHom.Finite.to_isIntegral`) followed by a surjection
     (`RingHom.isIntegral_of_surjective`, `RingHom.IsIntegral.trans`).
   - `isJacobsonRing_of_isIntegral'` makes `I' ⧸ p'` a Jacobson ring; it is a domain, so `⊥` is radical and
     `(⊥ : Ideal (I' ⧸ p')).jacobson = ⊥` (`IsJacobsonRing.out`); `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`.
2. `isJacobsonRing`: `isJacobsonRing_iff_prime_eq.2 fun P hP ↦ ?_`; `by_cases hP0 : P = ⊥` (use `h0`);
   otherwise `(h.jacobson_eq_radical hP0).trans hP.radical`.
#### Mathlib lemmas needed
`Ideal.radical_le_jacobson`, `Ideal.radical_eq_sInf`, `Ideal.jacobson_mono`, `Ideal.map_isPrime_of_equiv`, `Ideal.map_jacobson_of_bijective`, `Ideal.map_of_equiv`, `Ideal.Quotient.factor`, `RingHom.Finite.to_isIntegral`, `RingHom.isIntegral_of_surjective`, `RingHom.IsIntegral.trans`, `isJacobsonRing_of_isIntegral'`, `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`, `isJacobsonRing_iff_prime_eq`, `Ideal.IsPrime.radical`.
#### Sources
[BGR] 5.2.5/3, `bgr-5.2.md:299–329`; 5.2.6/3, `bgr-5.2.md:392–396`; decomposition L10.6, L10.7.
#### Generality decision
`a ≠ ⊥` is necessary (`k⟦X⟧` over `k`). The hypothesis `h0` of `isJacobsonRing` is BGR 5.1.3/3 for the Tate algebra.

### [CLEANUP-16] Run /cleanup on `Rueckert.lean`
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: T046 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:20: Rueckert.lean (T044–T046 part) runLinter clean, widths ≤ 100, no deprecated names (Ideal.bot_prime replaced).
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T047] Rückert overrings: factoriality
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: CLEANUP-16 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:20: uniqueFactorizationMonoid via private forall_mem_of_prod_mem, exists_monic_prime_factors (normalise by the unit leading coefficient; Associates.prod_mk), prime_map (quotient domain through axiom 2, MulEquiv.isDomain); std axioms.
- **Leaves**: L10.8

#### Statement
```lean
theorem uniqueFactorizationMonoid (h : IsRueckert φ W) [IsDomain I]
    [UniqueFactorizationMonoid I] [IsDomain I'] : UniqueFactorizationMonoid I' := by sorry
```
#### Proof sketch
`UniqueFactorizationMonoid.of_exists_prime_factors fun f hf ↦ ?_`.
1. `obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf`; `hm := h.monic ω hω`.
2. In the factorial ring `I[X]` (`Polynomial.uniqueFactorizationMonoid`):
   `obtain ⟨s, hs, hsω⟩ := UniqueFactorizationMonoid.exists_prime_factors ω hm.ne_zero`. Each `q ∈ s` divides
   `ω`, so its leading coefficient is a unit (`Polynomial.Monic.isUnit_leadingCoeff_of_dvd hm`); replace `q`
   by the monic associate `q' := C ↑(u⁻¹) * q`, still prime (`Associated.prime`). The product of the `q'`
   is monic (`Polynomial.monic_multiset_prod_of_monic`) and associated to `ω`, hence equal
   (`Polynomial.eq_of_monic_of_associated`).
3. Private lemma, by `Multiset.induction_on`: if every member of `s'` is monic and `s'.prod ∈ W`, every member
   is in `W` (`h.of_mul` on `q ::ₘ s'`, `Multiset.prod_cons`).
4. For `q' ∈ W` prime in `I[X]`: `I[X] ⧸ span {q'}` is a domain (`Ideal.span_singleton_prime`,
   `Ideal.Quotient.isDomain_iff_prime`), so `I' ⧸ (span {q'}).map φ` is a domain (`RingEquiv.ofBijective` of
   axiom (2), `MulEquiv.isDomain`), so `span {φ q'}` is prime (`Ideal.map_span`), so `φ q'` is prime
   (`φ q' ≠ 0` by `h.injective`).
5. `φ ω = (s'.map φ).prod` (`map_multiset_prod`), `σ f = ↑e⁻¹ * φ ω`, so
   `f = σ.symm ↑e⁻¹ * ((s'.map φ).map σ.symm).prod`; the members are prime (`MulEquiv.prime_iff`), and the
   product is associated to `f` (unit `σ.symm ↑e⁻¹`).
#### Mathlib lemmas needed
`UniqueFactorizationMonoid.of_exists_prime_factors`, `UniqueFactorizationMonoid.exists_prime_factors`, `Polynomial.uniqueFactorizationMonoid`, `Polynomial.Monic.isUnit_leadingCoeff_of_dvd`, `Polynomial.eq_of_monic_of_associated`, `Polynomial.monic_multiset_prod_of_monic`, `Associated.prime`, `Ideal.span_singleton_prime`, `Ideal.Quotient.isDomain_iff_prime`, `MulEquiv.isDomain`, `MulEquiv.prime_iff`, `map_multiset_prod`, `Multiset.induction_on`.
#### Sources
[BGR] 5.2.5/4, `bgr-5.2.md:336–364`; decomposition L10.8.
#### Generality decision
`I` a factorial domain, `I'` a domain. BGR's direct Gauss-lemma argument is replaced by "`I[X]` is factorial", which BGR itself names as the reason (`bgr-5.2.md:341–342`).

### [T048] Rückert overrings: the dimension goes up by one
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: T047 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:20: ringKrullDim_quotient_le, ringKrullDim_le (subsingleton case + quotient_le via Ideal.quotientEquiv and factor), ringKrullDim_add_one_le (quotientSpanXSubCAlgEquiv 0 after quotEquivOfEq); std axioms.
- **Leaves**: L10.9–L10.11

#### Statement
```lean
theorem ringKrullDim_quotient_le (h : IsRueckert φ W) {ω : I[X]} (hω : ω ∈ W) :
    ringKrullDim (I' ⧸ (Ideal.span {ω}).map φ) ≤ ringKrullDim I := by sorry
theorem ringKrullDim_le (h : IsRueckert φ W) : ringKrullDim I' ≤ ringKrullDim I + 1 := by sorry
theorem ringKrullDim_add_one_le (h : IsRueckert φ W) [IsDomain I'] (hX : (X : I[X]) ∈ W) :
    ringKrullDim I + 1 ≤ ringKrullDim I' := by sorry
```
#### Proof sketch
1. `ringKrullDim_quotient_le`: `ringKrullDim_le_of_isIntegral _ (h.finite_mk_comp_C hω).to_isIntegral`.
2. `ringKrullDim_le`: `rcases subsingleton_or_nontrivial I`. Subsingleton: `I[X]` and then `I'` are trivial
   (`φ 1 = 1`, `φ 0 = 0`), `ringKrullDim_eq_bot_of_subsingleton`, `bot_le`. Nontrivial:
   `ringKrullDim_le_add_one_of_forall_quotient_le ringKrullDim_nonneg_of_nontrivial fun p q hp hq hqp ↦ ?_`;
   `p ≠ ⊥` (`bot_le.trans_lt hqp`); `obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map hp0`;
   `R ⧸ p ≃+* R ⧸ p.map σ` (`Ideal.quotientEquiv p _ σ rfl`, `ringKrullDim_eq_of_ringEquiv`);
   `(Ideal.span {ω}).map φ ≤ p.map σ`, so `Ideal.Quotient.factor` is surjective and
   `ringKrullDim_le_of_surjective`; then item 1.
3. `ringKrullDim_add_one_le`: `x := φ X ≠ 0` (`h.injective`, `Polynomial.X_ne_zero`; `I` is nontrivial because
   `I'` is), so `x ∈ nonZeroDivisors I'` (`mem_nonZeroDivisors_of_ne_zero`).
   `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` gives `ringKrullDim (I' ⧸ span {x}) + 1 ≤ ringKrullDim I'`.
   And `I' ⧸ span {x} ≃+* I`: `span {x} = (span {X}).map φ` (`Ideal.map_span`), axiom (2) for `X`
   (`RingEquiv.ofBijective`), and `Polynomial.quotientSpanXSubCAlgEquiv 0` after `X = X - C 0`;
   `ringKrullDim_eq_of_ringEquiv`.
#### Mathlib lemmas needed
`RingHom.Finite.to_isIntegral`, `ringKrullDim_eq_bot_of_subsingleton`, `ringKrullDim_nonneg_of_nontrivial`, `Ideal.quotientEquiv`, `ringKrullDim_eq_of_ringEquiv`, `Ideal.Quotient.factor`, `ringKrullDim_le_of_surjective`, `mem_nonZeroDivisors_of_ne_zero`, `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, `Polynomial.quotientSpanXSubCAlgEquiv`, `Polynomial.X_ne_zero`, `Ideal.map_span`.
#### Sources
[BGR] 6.1.2, Remark, `bgr-6.1.2.md:49–57`; [Bo] 1.2/10, `bosch-lectures.txt:618–632`; decomposition L10.9–L10.11.
#### Generality decision
The upper bound replaces BGR's use of 7.1.1/3 (erratum E5). The lower bound needs `X ∈ W` and a domain. `ringKrullDim_eq` is already assembled in the skeleton.

### [CLEANUP-17] Run /cleanup on `Rueckert.lean`
- **Status**: done (2026-10-02) · **File**: `Rueckert.lean` · **Depends on**: T048 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:20: Rueckert.lean sorry-free, runLinter clean, widths ≤ 100, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T049] The Tate algebra is a Rückert overring
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Rueckert.lean` · **Depends on**: CLEANUP-13, CLEANUP-15 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:22: isRueckert_ofPolynomial: four fields as planned; axiom (3) from exists_shear_isMulDistinguishedX0 + preparation, change to ↑u⁻¹ * shear f; std axioms.
- **Leaves**: L11.1

#### Statement
```lean
theorem isRueckert_ofPolynomial (K : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (n : ℕ) :
    IsRueckert (ofPolynomial K n) {ω | IsWeierstrassPolynomial K n ω} := by sorry
```
#### Proof sketch
`refine ⟨ofPolynomial_injective, fun _ hω ↦ hω.monic, fun _ _ hp hq h ↦ IsWeierstrassPolynomial.of_mul hp hq h,
fun _ hω ↦ IsWeierstrassPolynomial.bijective_quotientMap hω, fun f hf ↦ ?_⟩` (the first four fields compile
as written: `scratch/spot3.lean`, item 1). For axiom (3):
`obtain ⟨e, s, hs⟩ := exists_shear_isMulDistinguishedX0 hf`;
`obtain ⟨ω, u, hω, -, hu⟩ := exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 hs`;
`exact ⟨(shear K n e).toRingEquiv, u⁻¹, ω, hω, by rw [show (shear K n e).toRingEquiv f = shear K n e f from rfl, hu, Units.inv_mul_cancel_left]⟩`.
#### Mathlib lemmas needed
`AlgEquiv.toRingEquiv`, `Units.inv_mul_cancel_left`.
#### Sources
[BGR] 5.2.5–5.2.6, `bgr-5.2.md:282–283`, `:366–368`; decomposition L11.1.
#### Generality decision
`K` complete, as an explicit binder (the section-variable trap, defect D5).

### [CLEANUP-ALL-2] Run /cleanup-all before milestone M2 (T050)
- **Status**: done (2026-10-02) · **Depends on**: T049, CLEANUP-12, CLEANUP-13, CLEANUP-15, CLEANUP-17 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:22: Sweep: TateAlgebra/{Distinguished,Finiteness,Chart,Rueckert} + Rueckert build with no warnings, runLinter clean on all five, widths ≤ 100, std axioms on the milestone declarations.
- Sweep before the milestone: `TateAlgebra/{Distinguished, Finiteness, Chart, Rueckert}.lean` and `Rueckert.lean`. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T050] `Tₙ` is noetherian, factorial, Jacobson, of dimension `n`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Rueckert.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: instances + theorem (milestone M2) · **Milestone**: M2
- **Progress**: 2026-10-02T15:22: MILESTONE M2: IsNoetherianRing, UniqueFactorizationMonoid, IsJacobsonRing instances on TateAlgebra K n and ringKrullDim_eq (= n), each by induction with Restricted.isEmptyEquiv at 0; IsIntegrallyClosed example compiles; sorry-free, std axioms.
- **Leaves**: L11.2–L11.5

#### Statement
```lean
instance instIsNoetherianRing (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : IsNoetherianRing (TateAlgebra K n) := by sorry
instance instUniqueFactorizationMonoid (K : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (n : ℕ) : UniqueFactorizationMonoid (TateAlgebra K n) := by sorry
instance instIsJacobsonRing (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : IsJacobsonRing (TateAlgebra K n) := by sorry
theorem ringKrullDim_eq (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : ringKrullDim (TateAlgebra K n) = n := by sorry
```
#### Proof sketch
Each by `induction n`, with `e₀ : TateAlgebra K 0 ≃+* K := Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)`.
1. `instIsNoetherianRing`: base `isNoetherianRing_of_ringEquiv K e₀.symm`; step
   `(isRueckert_ofPolynomial K n).isNoetherianRing` (both compile: `spot3.lean`, items 2–3).
2. `instUniqueFactorizationMonoid`: base `e₀.toMulEquiv.symm.uniqueFactorizationMonoid inferInstance` (a field
   is factorial); step `(isRueckert_ofPolynomial K n).uniqueFactorizationMonoid` (the `IsDomain` instances are
   T002's).
3. `instIsJacobsonRing`: base `isJacobsonRing_of_surjective ⟨(e₀.symm : K →+* _), e₀.symm.surjective⟩`; step
   `(isRueckert_ofPolynomial K n).isJacobsonRing jacobson_bot` (`spot3.lean`, item 3'').
4. `ringKrullDim_eq`: base `(ringKrullDim_eq_of_ringEquiv e₀).trans ringKrullDim_eq_zero_of_field`; step
   `(isRueckert_ofPolynomial K n).ringKrullDim_eq (by simpa using isWeierstrassPolynomial_X_pow 1)`
   (`spot3.lean`, item 3'), the induction hypothesis, and `Nat.cast_add_one`-style casts in `WithBot ℕ∞`.
The `example` for `IsIntegrallyClosed` below the factorial instance already compiles.
#### Mathlib lemmas needed
`isNoetherianRing_of_ringEquiv`, `MulEquiv.uniqueFactorizationMonoid`, `isJacobsonRing_of_surjective`, `ringKrullDim_eq_of_ringEquiv`, `ringKrullDim_eq_zero_of_field`. Floor: `Restricted.isEmptyEquiv`.
#### Sources
[BGR] 5.2.6/1–3, `bgr-5.2.md:366–396`; 6.1.2, Remark, `bgr-6.1.2.md:49–57`; [Bo] 1.2/13–15, `bosch-lectures.txt:676–743`; decomposition L11.2–L11.5.
#### Generality decision
Milestone M2. Instances on `TateAlgebra K n` for a complete `K`; normality follows by `inferInstance`.

### [CLEANUP-18] Run /cleanup on `TateAlgebra/Rueckert.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Rueckert.lean` · **Depends on**: T050 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:22: TateAlgebra/Rueckert.lean sorry-free, runLinter clean, widths ≤ 100.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T051] Bald subrings and the localisation at elements of norm one
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T15:31: IsBald.mono, le_unitLocalization, mem_unitLocalization_iff (closure_induction), IsBald.unitLocalization, isBRing_unitLocalization; std axioms.
- **Leaves**: L12.1–L12.5

#### Statement
```lean
theorem IsBald.mono {S S' : Subring K} (h : S ≤ S') (hS' : S'.IsBald) : S.IsBald := by sorry
theorem le_unitLocalization (S : Subring K) : S ≤ S.unitLocalization := by sorry
theorem mem_unitLocalization_iff {S : Subring K} {x : K} :
    x ∈ S.unitLocalization ↔ ∃ s ∈ S, ∃ u ∈ S, ‖u‖ = 1 ∧ x = s / u := by sorry
theorem IsBald.unitLocalization {S : Subring K} (hS : S.IsBald) : S.unitLocalization.IsBald := by sorry
theorem isBRing_unitLocalization {S : Subring K} (hS : ∀ a ∈ S, ‖a‖ ≤ 1) :
    S.unitLocalization.IsBRing := by sorry
```
#### Proof sketch
1. `IsBald.mono`: `⟨fun a ha ↦ hS'.norm_le_one a (h ha), hS'.exists_norm_le.imp fun ε hε ↦ ⟨hε.1, fun a ha ↦ hε.2 a (h ha)⟩⟩`.
2. `le_unitLocalization`: `fun x hx ↦ Subring.subset_closure (Or.inl hx)`.
3. `mem_unitLocalization_iff`: `←`: `rintro ⟨s, hs, u, hu, hu1, rfl⟩`; `div_eq_mul_inv`, `mul_mem` of
   `subset_closure (Or.inl hs)` and `subset_closure (Or.inr ⟨u, hu, hu1, rfl⟩)`. `→`:
   `Subring.closure_induction` with the predicate `∃ s ∈ S, ∃ u ∈ S, ‖u‖ = 1 ∧ x = s / u`: generators `s`
   (`s / 1`) and `u⁻¹` (`1 / u`); `0`, `1`; sums `(s₁ * u₂ + s₂ * u₁) / (u₁ * u₂)` (`div_add_div`, `norm_mul`,
   denominators nonzero since their norm is `1`); negation; products (`div_mul_div_comm`).
4. `IsBald.unitLocalization`: with item 3, `‖s / u‖ = ‖s‖` (`norm_div`, `hu1`, `div_one`); both fields
   follow from those of `S` with the same `ε`.
5. `isBRing_unitLocalization`: norms as in item 4; if `‖s / u‖ = 1` then `‖s‖ = 1`, and
   `(s / u)⁻¹ = u / s` (`inv_div`) is in the localisation by item 3 (`←`).
#### Mathlib lemmas needed
`Subring.subset_closure`, `Subring.closure_induction`, `div_add_div`, `div_mul_div_comm`, `norm_div`, `norm_mul`, `inv_div`.
#### Sources
[Bo] 1.3/2–3, `bosch-lectures.txt:767–772`, `:784–785`, `:806–807`; decomposition L12.1–L12.5.
#### Generality decision
Subrings of a normed field; no ultrametric hypothesis is needed in this ticket.

### [T052] The prime subring is bald; adjoining small elements
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: T051 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T15:31: isBald_bot (Nat.find on positive naturals of norm < 1; casts via congrArg Nat.cast since K may have positive characteristic — exact_mod_cast needs CharZero), closure_union_of_norm_le; import Mathlib.Analysis.Normed.Ring.Ultra added; std axioms.
- **Leaves**: L12.6, L12.7

#### Statement
```lean
theorem isBald_bot : (⊥ : Subring K).IsBald := by sorry
theorem IsBald.closure_union_of_norm_le {S : Subring K} (hS : S.IsBald) {T : Set K} {ε : ℝ}
    (hε : ε < 1) (hT : ∀ x ∈ T, ‖x‖ ≤ ε) : (closure ((S : Set K) ∪ T)).IsBald := by sorry
```
#### Proof sketch
1. `isBald_bot`: elements of `⊥` are integer casts (`Subring.mem_bot`), of norm `≤ 1`
   (`IsUltrametricDist.norm_intCast_le_one`). For the bound: `by_cases hex : ∃ g : ℕ, 0 < g ∧ ‖(g : K)‖ < 1`.
   - No: `ε := 0`. If `‖(z : K)‖ < 1` then `z.natAbs = 0` (else it is a positive natural of norm `< 1`:
     `Int.natAbs_eq`, `norm_neg`), so `z = 0` and the norm is `0`.
   - Yes: `g := Nat.find hex`, `ε := ‖(g : K)‖`. For `z` with `‖(z : K)‖ < 1`, `m := z.natAbs`,
     `‖(m : K)‖ = ‖(z : K)‖`; write `m = g * (m / g) + m % g` (`Nat.div_add_mod`); then
     `‖((m % g : ℕ) : K)‖ ≤ max ‖(m : K)‖ ‖(g : K)‖ < 1` (cast the identity, ultrametric), and `m % g < g`
     with minimality (`Nat.find_min`) forces `m % g = 0`; so `‖(m : K)‖ = ‖(g : K)‖ * ‖((m / g : ℕ) : K)‖ ≤ ε`
     (`IsUltrametricDist.norm_natCast_le_one`).
2. `IsBald.closure_union_of_norm_le`: `obtain ⟨εS, hεS, hS'⟩ := hS.exists_norm_le`; `δ := max ε 0`;
   `Subring.closure_induction` with the predicate `∃ s ∈ S, ∃ z, ‖z‖ ≤ δ ∧ x = s + z`: generators (`s + 0`,
   `0 + t`), `0`, `1`, sums and negation (ultrametric), products
   `(s₁ + z₁) * (s₂ + z₂) = s₁ * s₂ + (s₁ * z₂ + z₁ * s₂ + z₁ * z₂)` with each term of norm `≤ δ` (`‖sᵢ‖ ≤ 1`,
   `δ < 1`). Then: norm `≤ 1` by the ultrametric inequality; if `‖s + z‖ < 1` then `‖s‖ < 1` (otherwise
   `‖s‖ = 1 > ‖z‖` and `‖s + z‖ = 1` by `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), so
   `‖s‖ ≤ εS` and `‖s + z‖ ≤ max εS δ < 1`.
#### Mathlib lemmas needed
`Subring.mem_bot`, `IsUltrametricDist.norm_intCast_le_one`, `IsUltrametricDist.norm_natCast_le_one`, `Int.natAbs_eq`, `Nat.find`, `Nat.find_min`, `Nat.div_add_mod`, `Subring.closure_induction`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.
#### Sources
[Bo] 1.3/3, `bosch-lectures.txt:777–780`; decomposition L12.6, L12.7.
#### Generality decision
Any nonarchimedean normed field, any characteristic. `Int.cast_natAbs` does not exist at the pin; use `Int.natAbs_eq`.

### [T053] Adjoining an element of norm one to a bald B-ring
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: T052 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T15:31: exists_monic_norm_aeval_lt_one (low part up to the last unit coefficient, private norm_aeval_le / norm_aeval_lt_one), isBald_closure_insert (Nat.find minimal monic + modByMonic); imports Polynomial.Div + open scoped Polynomial; std axioms.
- **Leaves**: L12.8, L12.9

#### Statement
```lean
theorem IsBRing.exists_monic_norm_aeval_lt_one {S : Subring K} (hS : S.IsBRing) {a : K}
    (ha : ‖a‖ = 1) {p : Polynomial S} (hp : ‖Polynomial.aeval a p‖ < 1)
    (hc : ∃ i, ‖(p.coeff i : K)‖ = 1) :
    ∃ g : Polynomial S, g.Monic ∧ g.natDegree ≤ p.natDegree ∧ ‖Polynomial.aeval a g‖ < 1 := by sorry
theorem IsBRing.isBald_closure_insert {S : Subring K} (hB : S.IsBRing) (hS : S.IsBald) {a : K}
    (ha : ‖a‖ = 1) : (closure (insert a (S : Set K))).IsBald := by sorry
```
#### Proof sketch
1. `IsBRing.exists_monic_norm_aeval_lt_one`. Let `d` be the largest `i ≤ p.natDegree` with
   `‖(p.coeff i : K)‖ = 1` (`Finset.exists_max_image` on the filtered range, nonempty by `hc`).
   `low := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (p.coeff i)`, and `p - low` has all coefficients
   of norm `< 1`, so `‖aeval a (p - low)‖ < 1` (`Polynomial.aeval_eq_sum_range`, the ultrametric bound on a
   finite sum, `‖a ^ i‖ = 1`); hence `‖aeval a low‖ < 1`. The coefficient `p.coeff d` has norm one, so its
   inverse lies in `S` (`hS.inv_mem`): `u : S`. `g := Polynomial.C u * low` is monic of degree `d`
   (coefficient at `d` is `u * p.coeff d = 1`, higher coefficients vanish), `g.natDegree = d ≤ p.natDegree`,
   and `‖aeval a g‖ = ‖(u : K)‖ * ‖aeval a low‖ < 1`.
2. `IsBRing.isBald_closure_insert`.
   - Every element of `closure (insert a S)` is `Polynomial.aeval a p` for some `p : Polynomial S`
     (`Subring.closure_induction`: `a = aeval a X`, `s = aeval a (C ⟨s, _⟩)`, ring operations by `map_*`).
   - `‖aeval a p‖ ≤ 1` (finite ultrametric sum, `hB.norm_le_one`, `ha`).
   - Bald constant: `obtain ⟨εS, hεS, hS'⟩ := hS.exists_norm_le`.
     `by_cases hex : ∃ g : Polynomial S, g.Monic ∧ ‖aeval a g‖ < 1`.
     *No*: if `‖aeval a p‖ < 1`, no coefficient of `p` has norm one (item 1), so all are `≤ εS` and
     `‖aeval a p‖ ≤ εS`.
     *Yes*: choose `g` of minimal degree (`Nat.find` on `∃ g, g.Monic ∧ ‖aeval a g‖ < 1 ∧ g.natDegree = n`);
     `ε := max ‖aeval a g‖ εS`. For `f` with `‖aeval a f‖ < 1`: `f = g * (f /ₘ g) + f %ₘ g`
     (`Polynomial.modByMonic_add_div`), `r := f %ₘ g`, `r.natDegree < g.natDegree` when `g ≠ 1`
     (`Polynomial.natDegree_modByMonic_lt`; if `g = 1` then `‖aeval a g‖ = 1`, impossible).
     `‖aeval a r‖ < 1`. If some coefficient of `r` had norm one, item 1 would give a monic polynomial of
     smaller degree — contradiction. So `‖aeval a r‖ ≤ εS` and
     `‖aeval a f‖ ≤ max (‖aeval a g‖ * ‖aeval a (f /ₘ g)‖) ‖aeval a r‖ ≤ ε`.
#### Mathlib lemmas needed
`Finset.exists_max_image`, `Polynomial.aeval_eq_sum_range`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Polynomial.modByMonic_add_div`, `Polynomial.natDegree_modByMonic_lt`, `Nat.find`, `Nat.find_min`, `Subring.closure_induction`, `Polynomial.aeval_X`, `Polynomial.aeval_C`.
#### Sources
[Bo] 1.3/3, `bosch-lectures.txt:781–805`; decomposition L12.8, L12.9.
#### Generality decision
Bosch's dichotomy (`ã` transcendental or algebraic over `S̃`) is phrased without residue fields: either no monic `g` has `‖g(a)‖ < 1`, or one of minimal degree exists.

### [CLEANUP-19] Run /cleanup on `Bald.lean`
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: T053 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:31: Bald.lean runLinter clean, widths ≤ 100, finset_sum_coeff → finsetSum_coeff.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T054] The subring generated by a null family is bald
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: CLEANUP-19 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:31: IsBald.closure_insert (two cases), private isBald_closure_finset (Finset.induction_on), isBald_closure_range; std axioms.
- **Leaves**: L12.10, L12.11

#### Statement
```lean
theorem IsBald.closure_insert {S : Subring K} (hS : S.IsBald) {a : K} (ha : ‖a‖ ≤ 1) :
    (closure (insert a (S : Set K))).IsBald := by sorry
theorem isBald_closure_range {ι : Type*} {a : ι → K} (ha : ∀ i, ‖a i‖ ≤ 1)
    (ha0 : Tendsto a cofinite (𝓝 0)) : (closure (Set.range a)).IsBald := by sorry
```
#### Proof sketch
1. `IsBald.closure_insert`: `rcases ha.lt_or_eq with h | h`.
   - `‖a‖ < 1`: `Set.insert_eq`, `Set.union_comm`, then
     `hS.closure_union_of_norm_le h fun x hx ↦ (Set.mem_singleton_iff.1 hx ▸ le_rfl)`.
   - `‖a‖ = 1`: `S' := S.unitLocalization` is bald (`hS.unitLocalization`) and a B-ring
     (`isBRing_unitLocalization hS.norm_le_one`), so `closure (insert a S')` is bald (T053), and
     `closure (insert a S) ≤ closure (insert a S')` (`Subring.closure_mono`, `Set.insert_subset_insert`,
     `le_unitLocalization`); `IsBald.mono`.
2. `isBald_closure_range`: `F := {i | (1/2 : ℝ) < ‖a i‖}` is finite (`ha0.norm`, `eventually_le_const`-style:
   `Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`).
   - `R₀ := closure (a '' F)` is bald: `Set.Finite.induction_on` on the finite set `a '' F`; base
     `Subring.closure_empty` and `isBald_bot`; step `closure (insert x s) = closure (insert x ↑(closure s))`
     (`Subring.closure_union`, `Subring.closure_eq`, `Set.insert_eq`) and item 1 (`‖x‖ ≤ 1` from `ha`).
   - `closure (↑R₀ ∪ a '' Fᶜ)` is bald by `closure_union_of_norm_le` with `ε = 1/2`.
   - `closure (range a) ≤` that (`Subring.closure_mono`: `range a ⊆ a '' F ∪ a '' Fᶜ`,
     `Subring.subset_closure`); `IsBald.mono`.
#### Mathlib lemmas needed
`Subring.closure_mono`, `Subring.closure_empty`, `Subring.closure_eq`, `Subring.closure_union`, `Set.Finite.induction_on`, `Set.Finite.image`, `Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`, `Set.insert_eq`.
#### Sources
[Bo] 1.3/3, `bosch-lectures.txt:774–785`; decomposition L12.10, L12.11.
#### Generality decision
A family indexed by any type, null along the cofinite filter (Bosch's "zero sequence"). Nullity is necessary over a densely valued field.

### [CLEANUP-20] Run /cleanup on `Bald.lean`
- **Status**: done (2026-10-02) · **File**: `Bald.lean` · **Depends on**: T054 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:31: Bald.lean sorry-free, runLinter clean, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T055] Orthonormal families: finite sums
- **Status**: done (2026-10-02) · **File**: `PadicFunctionalAnalysis/Orthonormal.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-10-02T15:34: norm_coeff_le_norm_sum, norm_sum_le, linearIndependent via new public nnnorm_smul_eq; std axioms.
- **Leaves**: L13.1–L13.3

#### Statement
```lean
theorem norm_coeff_le_norm_sum (he : IsOrthonormalFamily K e) (s : Finset I) (a : I → K) {i : I}
    (hi : i ∈ s) : ‖a i‖ ≤ ‖∑ j ∈ s, a j • e j‖ := by sorry
theorem norm_sum_le (he : IsOrthonormalFamily K e) (s : Finset I) (a : I → K) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i ∈ s, ‖a i‖ ≤ C) : ‖∑ i ∈ s, a i • e i‖ ≤ C := by sorry
theorem linearIndependent (he : IsOrthonormalFamily K e) : LinearIndependent K e := by sorry
```
#### Proof sketch
`he.2 s a : ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊`, and `‖a i • e i‖₊ = ‖a i‖₊`
(`nnnorm_smul`, `he.1 i` in `ℝ≥0`, `mul_one`).
1. `norm_coeff_le_norm_sum`: in `ℝ≥0`, `‖a i‖₊ = ‖a i • e i‖₊ ≤ s.sup _ = ‖∑‖₊` (`Finset.le_sup hi`); coerce
   (`NNReal.coe_le_coe`, `coe_nnnorm`).
2. `norm_sum_le`: lift `C` to `ℝ≥0` (`C.toNNReal`, `Real.coe_toNNReal C hC`); `rw [he.2]`;
   `Finset.sup_le fun i hi ↦ ?_`.
3. `linearIndependent`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`;
   `norm_le_zero_iff.1 ((he.norm_coeff_le_norm_sum s g hi).trans_eq (by rw [hg, norm_zero]))`.
#### Mathlib lemmas needed
`nnnorm_smul`, `Finset.le_sup`, `Finset.sup_le`, `linearIndependent_iff'`, `norm_le_zero_iff`, `NNReal.coe_le_coe`, `Real.coe_toNNReal`.
#### Sources
[Bo] 1.3/5, `bosch-lectures.txt:820–831`; PFA roadmap convention 5, §2.2.1; decomposition L13.1–L13.3.
#### Generality decision
A normed space over a normed field; no ultrametricity or completeness. `hC : 0 ≤ C` covers the empty sum.

### [T056] Orthonormal families: convergent sums
- **Status**: done (2026-10-02) · **File**: `PadicFunctionalAnalysis/Orthonormal.lean` · **Depends on**: T055 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-02T15:34: tendsto_cofinite_of_hasSum, norm_coeff_le_of_hasSum, norm_le_of_hasSum, eq_of_hasSum (HasSum unfolded to Tendsto over atTop by an explicit have); std axioms.
- **Leaves**: L13.4–L13.7

#### Statement
```lean
theorem tendsto_cofinite_of_hasSum (he : IsOrthonormalFamily K e) {a : I → K} {x : V}
    (hx : HasSum (fun i ↦ a i • e i) x) : Tendsto a cofinite (𝓝 0) := by sorry
theorem norm_coeff_le_of_hasSum (he : IsOrthonormalFamily K e) {a : I → K} {x : V}
    (hx : HasSum (fun i ↦ a i • e i) x) (i : I) : ‖a i‖ ≤ ‖x‖ := by sorry
theorem norm_le_of_hasSum (he : IsOrthonormalFamily K e) {a : I → K} {x : V}
    (hx : HasSum (fun i ↦ a i • e i) x) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖a i‖ ≤ C) : ‖x‖ ≤ C := by sorry
theorem eq_of_hasSum (he : IsOrthonormalFamily K e) {a b : I → K} {x : V}
    (ha : HasSum (fun i ↦ a i • e i) x) (hb : HasSum (fun i ↦ b i • e i) x) : a = b := by sorry
```
#### Proof sketch
1. `tendsto_cofinite_of_hasSum`: `tendsto_zero_iff_norm_tendsto_zero.2 ?_`;
   `hx.summable.tendsto_cofinite_zero.norm` rewritten with `norm_smul`, `he.1`, `mul_one`, `norm_zero`.
2. `norm_coeff_le_of_hasSum`: `hx.norm : Tendsto (fun s ↦ ‖∑ j ∈ s, a j • e j‖) atTop (𝓝 ‖x‖)`;
   `ge_of_tendsto` (or `le_of_tendsto'` on the constant) with
   `(Filter.eventually_ge_atTop {i}).mono fun s hs ↦ he.norm_coeff_le_norm_sum s a (hs (Finset.mem_singleton_self i))`.
3. `norm_le_of_hasSum`: `le_of_tendsto' hx.norm fun s ↦ he.norm_sum_le s a hC fun i _ ↦ h i`.
4. `eq_of_hasSum`: `funext i`; `sub_eq_zero.1 (norm_le_zero_iff.1 ?_)`;
   `(he.norm_coeff_le_of_hasSum (a := a - b) (x := 0) ?_ i).trans_eq norm_zero`, the `HasSum` from
   `ha.sub hb` with `Pi.sub_apply`, `sub_smul`, `sub_self`.
#### Mathlib lemmas needed
`tendsto_zero_iff_norm_tendsto_zero`, `Summable.tendsto_cofinite_zero`, `Filter.Tendsto.norm`, `ge_of_tendsto`, `le_of_tendsto'`, `Filter.eventually_ge_atTop`, `HasSum.sub`, `sub_smul`.
#### Sources
[Bo] 1.3/5 (iii), `bosch-lectures.txt:829–831`; decomposition L13.4–L13.7.
#### Generality decision
No completeness: the expansions are hypotheses.

### [T057] Expansions in an orthonormal basis exist
- **Status**: done (2026-10-02) · **File**: `PadicFunctionalAnalysis/Orthonormal.lean` · **Depends on**: T056 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:34: summable_smul (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero), exists_hasSum per sketch (Finsupp.sum_of_support_subset needs g explicit); imports LinearCombination, InfiniteSum.Nonarchimedean, Topology.Sequences; std axioms.
- **Leaves**: L13.8, L13.9

#### Statement
```lean
theorem summable_smul [IsUltrametricDist V] [CompleteSpace V] (he : IsOrthonormalFamily K e)
    {a : I → K} (ha : Tendsto a cofinite (𝓝 0)) : Summable fun i ↦ a i • e i := by sorry
theorem exists_hasSum [CompleteSpace K] (he : IsOrthonormalBasis K e) (x : V) :
    ∃ a : I → K, HasSum (fun i ↦ a i • e i) x := by sorry
```
#### Proof sketch
1. `summable_smul`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; the terms tend to zero by
   `tendsto_zero_iff_norm_tendsto_zero` and `norm_smul`, `he.1`.
2. `IsOrthonormalBasis.exists_hasSum` (`K` complete — false otherwise, see the docstring).
   - `he.2 x : x ∈ closure (span K (range e))`; `mem_closure_iff_seq_limit` gives `u : ℕ → V` in the span
     with `u k → x`; `Finsupp.mem_span_range_iff_exists_finsupp` gives `l k : I →₀ K` with
     `(l k).sum (fun i c ↦ c • e i) = u k`.
   - For `k`, `m` and `i`: `‖l k i - l m i‖ ≤ ‖u k - u m‖` (`he.1.norm_coeff_le_norm_sum` on the finset
     `(l k).support ∪ (l m).support` for the family `l k - l m`; when `i` is outside both supports the left
     side is `0`).
   - So for each `i`, `k ↦ l k i` is Cauchy (`u` is Cauchy: `Filter.Tendsto.cauchySeq`); `a i` := its limit
     (`cauchySeq_tendsto_of_complete`). Passing to the limit in `m`: `‖l k i - a i‖ ≤ δ k` with
     `δ k := sup over m ≥ k of ‖u k - u m‖`, more simply: for `ε > 0` choose `N` with `‖u k - u m‖ ≤ ε` for
     `k, m ≥ N`; then `‖l k i - a i‖ ≤ ε` for `k ≥ N` and all `i` (`le_of_tendsto`).
   - `a → 0` cofinitely: outside `(l N).support`, `‖a i‖ ≤ ε`.
   - `y := ∑' i, a i • e i` exists (item 1), and `‖y - u k‖ ≤ ε` for `k ≥ N`
     (`he.1.norm_le_of_hasSum` for the family `a - l k`, whose sum is `y - u k`: `HasSum.sub` and
     `hasSum_sum_of_ne_finset_zero` for the finitely supported `l k`). Hence `u k → y`, and `y = x`
     (`tendsto_nhds_unique`).
#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_zero_iff_norm_tendsto_zero`, `mem_closure_iff_seq_limit`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Filter.Tendsto.cauchySeq`, `cauchySeq_tendsto_of_complete`, `le_of_tendsto`, `HasSum.sub`, `hasSum_sum_of_ne_finset_zero`, `tendsto_nhds_unique`.
#### Sources
[Bo] 1.3/5 (ii), `bosch-lectures.txt:820–826`; `:813–814` (`K` complete); decomposition L13.8, L13.9.
#### Generality decision
`[CompleteSpace K]` is necessary (defect D7: `ℚ ⊂ ℚ_p`). `summable_smul` needs only `V` complete and ultrametric.

### [CLEANUP-21] Run /cleanup on `PadicFunctionalAnalysis/Orthonormal.lean`
- **Status**: done (2026-10-02) · **File**: `PadicFunctionalAnalysis/Orthonormal.lean` · **Depends on**: T057 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:34: Orthonormal.lean sorry-free, runLinter clean, widths ≤ 100.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T058] Descent to a subfield; the residue field of a B-ring
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: CLEANUP-20 · **Parallel**: no · **Type**: lemma + definition
- **Progress**: 2026-10-02T15:41: mem_span_range_of_mapRange_mem_span (left inverse π of Algebra.linearMap; import LinearAlgebra.Basis.VectorSpace) and residueSubfield (six fields; inverse via eq_inv_of_mul_eq_one_left); std axioms.
- **Leaves**: L14.1, L14.2

#### Statement
```lean
theorem Finsupp.mem_span_range_of_mapRange_mem_span {F E : Type*} [Field F] [Field E]
    [Algebra F E] {N M : Type*} (v : M → N →₀ F) (w : N →₀ F)
    (h : Finsupp.mapRange (algebraMap F E) (map_zero _) w ∈
      Submodule.span E (Set.range fun μ ↦ Finsupp.mapRange (algebraMap F E) (map_zero _) (v μ))) :
    w ∈ Submodule.span F (Set.range v) := by sorry
def Subring.IsBRing.residueSubfield {S : Subring K} (hS : S.IsBRing) :
    Subfield (ResidueField (unitClosedBall K)) where
  carrier := {z | ∃ (s : K) (hs : s ∈ S),
    z = residue (unitClosedBall K) ⟨s, mem_unitClosedBall.2 (hS.norm_le_one s hs)⟩}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
  inv_mem' := by sorry
```
#### Proof sketch
1. `Finsupp.mem_span_range_of_mapRange_mem_span`. `ι := Algebra.linearMap F E` is injective
   (`(algebraMap F E).injective`); `obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 _)`,
   so `π (algebraMap F E c) = c`. `obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h` with
   `l : M →₀ E`. Claim `w = (l.mapRange π (map_zero π)).sum fun μ c ↦ c • v μ`; then
   `Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩`-style. Check at `n : N`: evaluate `hl` at `n`
   (`Finsupp.sum_apply`, `Finsupp.smul_apply`, `Finsupp.mapRange_apply`):
   `algebraMap (w n) = ∑ μ ∈ l.support, l μ * algebraMap (v μ n)`; apply `π` (`map_sum`), and
   `π (l μ * algebraMap c) = π (c • l μ) = c * π (l μ)` (`Algebra.smul_def`, `mul_comm`, `map_smul`).
   Terms with `π (l μ) = 0` are harmless (`Finsupp.sum_mapRange_index` or sum over `l.support`).
2. `residueSubfield`: the six fields. Write `ρ s hs := residue _ ⟨s, _⟩`. `one_mem'`, `zero_mem'`:
   `⟨1, S.one_mem, by simp⟩`-style (`map_one`, `map_zero`, the subtype is `1` / `0`). `add_mem'`,
   `mul_mem'`, `neg_mem'`: `⟨s + t, S.add_mem hs ht, by rw [← map_add]; rfl⟩` etc. `inv_mem'`: for
   `z = ρ s hs`, `rcases (hS.norm_le_one s hs).lt_or_eq`: if `‖s‖ < 1` then `z = 0` (`residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`) and `inv_zero`; if `‖s‖ = 1` then `s⁻¹ ∈ S` (`hS.inv_mem`), and
   `ρ s⁻¹ = z⁻¹` by `eq_inv_of_mul_eq_one_right` (`← map_mul`, the product in `K⁰` is `1`).
#### Mathlib lemmas needed
`LinearMap.exists_leftInverse_of_injective`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Finsupp.sum_apply`, `Finsupp.mapRange_apply`, `Algebra.smul_def`, `IsLocalRing.residue_eq_zero_iff`, `eq_inv_of_mul_eq_one_right`.
#### Sources
[Bo] 1.3/3 and 1.3/6, `bosch-lectures.txt:785–786`, `:869–874`; decomposition L14.1, L14.2.
#### Generality decision
Item 1 is pure linear algebra over a field extension `F → E` (false for rings). Item 2 is a `Subfield` of the residue field of `K`, so that Bosch's `S̃ ⊂ k` is literal.

### [T059] Independent reductions are orthonormal
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: CLEANUP-21 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:41: of_linearIndependent_residue: norm one via a nonzero residue coordinate; sup identity via a maximal coefficient, normalisation b = a μ₀⁻¹ * a, residues through private toUnitBall/toUnitBall_of_le; std axioms.
- **Leaves**: L14.3

#### Statement
```lean
theorem IsOrthonormalFamily.of_linearIndependent_residue (hx : IsOrthonormalFamily K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) (hc : ∀ μ ν, ‖c μ ν‖ ≤ 1)
    (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K) ⟨c μ ν, mem_unitClosedBall.2 (hc μ ν)⟩)
    (hli : LinearIndependent (ResidueField (unitClosedBall K)) r) : IsOrthonormalFamily K y := by sorry
```
#### Proof sketch
`refine ⟨fun μ ↦ ?_, fun s a ↦ ?_⟩`.
1. `‖y μ‖ = 1`: `≤` by `hx.norm_le_of_hasSum (hy μ) zero_le_one (hc μ)`. `≥`: `r μ ≠ 0`
   (`hli.ne_zero μ`), so some `ν` has `r μ ν ≠ 0`; by `hr` and `residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`, `¬ ‖c μ ν‖ < 1`, so `1 ≤ ‖c μ ν‖ ≤ ‖y μ‖` (`hx.norm_coeff_le_of_hasSum`).
2. The identity `‖∑ μ ∈ s, a μ • y μ‖₊ = s.sup fun μ ↦ ‖a μ • y μ‖₊`. Reduce to reals; `‖a μ • y μ‖ = ‖a μ‖`.
   - `≤`: `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
   - `≥`: let `μ₀ ∈ s` maximise `‖a μ‖` (`Finset.exists_max_image`; `s = ∅` is trivial); if `a μ₀ = 0` all are
     `0`. Otherwise `b μ := a μ / a μ₀`, `‖b μ‖ ≤ 1`, `b μ₀ = 1`, and it suffices that `1 ≤ ‖∑ μ ∈ s, b μ • y μ‖`.
     `HasSum (fun ν ↦ (∑ μ ∈ s, b μ * c μ ν) • x ν) (∑ μ ∈ s, b μ • y μ)` (`hasSum_sum`, `HasSum.const_smul`,
     `Finset.sum_smul`, `mul_smul`). The coefficients `d ν` lie in `K⁰`, with residues
     `(∑ μ ∈ s, b̃ μ • r μ) ν` (`map_sum`, `map_mul`, `hr`). Since `b̃ μ₀ = 1 ≠ 0` and `hli`, that combination
     is nonzero (`linearIndependent_iff'`), so some `ν` has `‖d ν‖ = 1`, and
     `hx.norm_coeff_le_of_hasSum _ ν` concludes.
#### Mathlib lemmas needed
`LinearIndependent.ne_zero`, `linearIndependent_iff'`, `hasSum_sum`, `HasSum.const_smul`, `Finset.exists_max_image`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsLocalRing.residue_eq_zero_iff`. Chain: `IsOrthonormalFamily.norm_le_of_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`.
#### Sources
[Bo] 1.3/6, `bosch-lectures.txt:849–851`; decomposition L14.3.
#### Generality decision
No baldness and no completeness: independence of the reductions alone gives orthonormality.

### [T060] Spanning reductions give approximation up to the bald constant
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: T058, T059 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T15:41: exists_norm_sub_le_of_span_residue per sketch (rF by Finsupp.onFinset, descent via T058, choose b from mem_residueSubfield, coefficient residues vanish); ε := max ε 0; std axioms.
- **Leaves**: L14.4

#### Statement
```lean
theorem exists_norm_sub_le_of_span_residue (hx : IsOrthonormalFamily K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) {S : Subring K} (hS : S.IsBald)
    (hcS : ∀ μ ν, c μ ν ∈ S) (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K)
      ⟨c μ ν, mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ ν))⟩)
    (hspan : Submodule.span (ResidueField (unitClosedBall K)) (Set.range r) = ⊤) :
    ∃ ε : ℝ, ε < 1 ∧ ∀ ν, ∃ z ∈ Submodule.span K (Set.range y), ‖x ν - z‖ ≤ ε := by sorry
```
#### Proof sketch
1. `S' := S.unitLocalization`, bald (`hS.unitLocalization`) and a B-ring
   (`isBRing_unitLocalization hS.norm_le_one`); `obtain ⟨ε, hε, hbald⟩ := hS'.exists_norm_le`;
   `F := hB.residueSubfield`. Use this `ε`.
2. The family over `F`: `rF μ : N →₀ F := Finsupp.onFinset (r μ).support (fun ν ↦ ⟨r μ ν, _⟩) _`, membership
   by `hr` and `c μ ν ∈ S ≤ S'`; `Finsupp.mapRange (algebraMap F _) _ (rF μ) = r μ`.
3. Fix `ν`. `Finsupp.single ν 1` lies in `span k (range r) = ⊤`, and it is the `mapRange` of
   `Finsupp.single ν (1 : F)`, so by T058 it lies in `span F (range rF)`:
   `obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 _` with `l : M →₀ F`. For `μ ∈ l.support`
   choose `b μ ∈ S'` with `l μ = ρ (b μ)` (`mem_residueSubfield`).
4. `z := ∑ μ ∈ l.support, b μ • y μ ∈ span K (range y)`. Expansion of `x ν - z` in `x`:
   `HasSum (fun ν' ↦ d ν' • x ν') (x ν - z)` with `d ν' := (if ν' = ν then 1 else 0) - ∑ μ ∈ l.support, b μ * c μ ν'`
   (`hasSum_ite_eq`-type for `x ν`, `hasSum_sum`, `HasSum.const_smul`, `HasSum.sub`).
5. `d ν' ∈ S'` (subring), and its residue is `(single ν 1 - ∑ l μ • r μ) ν' = 0` by `hl`; so `‖d ν'‖ < 1`,
   hence `‖d ν'‖ ≤ ε` (`hbald`). `hx.norm_le_of_hasSum _ (le of 0 ≤ ε) _` gives `‖x ν - z‖ ≤ ε`; `0 ≤ ε`
   because `0 ∈ S'` has norm `0 < 1`.
#### Mathlib lemmas needed
`Finsupp.onFinset`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Finsupp.mapRange_apply`, `hasSum_sum`, `HasSum.const_smul`, `HasSum.sub`, `hasSum_ite_eq`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.
#### Sources
[Bo] 1.3/6, `bosch-lectures.txt:851–876`; decomposition L14.4.
#### Generality decision
The uniform `ε` is the bald constant of the localisation of `S`. Baldness is necessary (counterexample in the module docstring). No completeness.

### [CLEANUP-22] Run /cleanup on `OrthonormalLift.lean`
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: T060 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:41: OrthonormalLift.lean (T058–T060) runLinter clean, widths ≤ 100.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T061] Lifting of orthonormal bases
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: CLEANUP-22 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T15:43: dense_span_of_forall_exists_norm_sub_le via floor AddSubgroup.dense_of_infDist_le with ε' = max ε 1/2 (omit [IsUltrametricDist K]); of_residue_basis assembled; std axioms.
- **Leaves**: L14.5, L14.6

#### Statement
```lean
theorem dense_span_of_forall_exists_norm_sub_le (hx : IsOrthonormalBasis K x) {ε : ℝ}
    (hε : ε < 1) (h : ∀ ν, ∃ z ∈ Submodule.span K (Set.range y), ‖x ν - z‖ ≤ ε) :
    Dense (Submodule.span K (Set.range y) : Set V) := by sorry
theorem IsOrthonormalBasis.of_residue_basis (hx : IsOrthonormalBasis K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) {S : Subring K} (hS : S.IsBald)
    (hcS : ∀ μ ν, c μ ν ∈ S) (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K)
      ⟨c μ ν, mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ ν))⟩)
    (hli : LinearIndependent (ResidueField (unitClosedBall K)) r)
    (hspan : Submodule.span (ResidueField (unitClosedBall K)) (Set.range r) = ⊤) :
    IsOrthonormalBasis K y := by sorry
```
#### Proof sketch
1. `dense_span_of_forall_exists_norm_sub_le`. `ε' := max ε (1/2)`, `0 < ε' < 1`, and `h` holds with `ε'`.
   `U := (Submodule.span K (range y)).toAddSubgroup`; apply
   `AddSubgroup.dense_of_infDist_le U ε' _ _ fun v ↦ ?_` (BGR 1.1.4/2, in the floor), i.e. show
   `Metric.infDist v U ≤ ε' * dist v 0`. `v = 0` is trivial. Otherwise:
   - by density of `span K (range x)` (`hx.2`) choose `v'` in it with `‖v - v'‖ ≤ ε' * ‖v‖`
     (`Metric.mem_closure_iff`); then `‖v'‖ ≤ ‖v‖` (ultrametric);
   - `v' = ∑ ν ∈ s, a ν • x ν` (`Finsupp.mem_span_range_iff_exists_finsupp`); choose `z ν` from `h`;
     `z' := ∑ ν ∈ s, a ν • z ν ∈ U`, and
     `‖v' - z'‖ = ‖∑ a ν • (x ν - z ν)‖ ≤ ε' * ‖v'‖` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
     `norm_smul`, `hx.1.norm_coeff_le_norm_sum`);
   - `‖v - z'‖ ≤ max ‖v - v'‖ ‖v' - z'‖ ≤ ε' * ‖v‖`, and `Metric.infDist_le_dist_of_mem`.
2. `IsOrthonormalBasis.of_residue_basis`:
   `⟨hx.1.of_linearIndependent_residue hy (fun μ ν ↦ hS.norm_le_one _ (hcS μ ν)) r hr hli, ?_⟩`, and for the
   density `obtain ⟨ε, hε, h⟩ := exists_norm_sub_le_of_span_residue hx.1 hy hS hcS r hr hspan`;
   `exact dense_span_of_forall_exists_norm_sub_le hx hε h`.
#### Mathlib lemmas needed
`Metric.mem_closure_iff`, `Metric.infDist_le_dist_of_mem`, `Finsupp.mem_span_range_iff_exists_finsupp`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsUltrametricDist.norm_add_le_max`. Floor: `AddSubgroup.dense_of_infDist_le`.
#### Sources
[Bo] 1.3/6, `bosch-lectures.txt:839–883`; BGR 1.1.4/2 (the floor's lemma); decomposition L14.5, L14.6.
#### Generality decision
The conclusion is the dense-span form of `IsOrthonormalBasis`, and holds without completeness of `K` or `V` (defect D4); Bosch's "by iteration" is the density lemma.

### [CLEANUP-23] Run /cleanup on `OrthonormalLift.lean`
- **Status**: done (2026-10-02) · **File**: `OrthonormalLift.lean` · **Depends on**: T061 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:43: OrthonormalLift.lean sorry-free, runLinter clean, widths ≤ 100.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T062] A basis of `k[X]^ι` adapted to a submodule
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Progress**: 2026-10-02T15:53: exists_basis_adaptedFamily via LinearIndepOn.extend twice (A₀ in range inl, then C); C ∩ range inl = A₀ by notMem_span_of_insert; span ⊤ through Pi.basis of basisMonomials; restrictScalars identity by span_induction + monomial_mul; std axioms.
- **Leaves**: L15.1

#### Statement
```lean
theorem exists_basis_adaptedFamily [Fintype ι] {r : ℕ} (h : Fin r → ι → MvPolynomial σ k) :
    ∃ (A : Set ((σ →₀ ℕ) × Fin r)) (B : Set (Σ _ : ι, σ →₀ ℕ)),
      LinearIndependent k (adaptedFamily h A B) ∧
        Submodule.span k (Set.range (adaptedFamily h A B)) = ⊤ ∧
          Submodule.span k (Set.range fun a : A ↦ monomial a.1.1 (1 : k) • h a.1.2) =
            (Submodule.span (MvPolynomial σ k) (Set.range h)).restrictScalars k := by sorry
```
#### Proof sketch
Write `P := MvPolynomial σ k`, `W := ι → P`, `G : (σ →₀ ℕ) × Fin r → W := fun a ↦ monomial a.1 1 • h a.2`,
`E : (Σ _ : ι, σ →₀ ℕ) → W := fun b ↦ Pi.single b.1 (monomial b.2 1)`, and `v := Sum.elim G E` on the index
type `J := ((σ →₀ ℕ) × Fin r) ⊕ (Σ _ : ι, σ →₀ ℕ)`.
1. `A₀ := (linearIndepOn_empty k v).extend (Set.empty_subset (Set.range Sum.inl))`: a subset of
   `range Sum.inl`, `LinearIndepOn k v A₀` (`LinearIndepOn.linearIndepOn_extend`), and
   `v '' range Sum.inl ⊆ span k (v '' A₀)` (`LinearIndepOn.subset_span_extend`).
2. `C := h₀.extend (A₀ ⊆ Set.univ)`: `A₀ ⊆ C` (`LinearIndepOn.subset_extend`), `LinearIndepOn k v C`, and
   `range v ⊆ span k (v '' C)`. Moreover `C ∩ range Sum.inl = A₀`: an index `Sum.inl a ∈ C \ A₀` would make
   `v` dependent on `A₀ ∪ {inl a} ⊆ C`, because `v (inl a) ∈ span k (v '' A₀)` (step 1) while
   `(hC.mono _).notMem_span_of_insert` says it is not (`LinearIndepOn.mono`, `LinearIndepOn.notMem_span_of_insert`).
3. `A := Sum.inl ⁻¹' C`, `B := Sum.inr ⁻¹' C`; the map `A ⊕ B → C` is a bijection and
   `adaptedFamily h A B = v ∘ (that map)`, so `LinearIndependent k (adaptedFamily h A B)`
   (`LinearIndepOn` is `LinearIndependent` of the restriction; `LinearIndependent.comp` with an injective map,
   or `linearIndependent_equiv`).
4. Span `= ⊤`: `range E` spans `W` over `k` — `E` is the basis `Pi.basis fun _ : ι ↦ basisMonomials σ k`
   (`Pi.basis_apply`, `basisMonomials_apply`; `scratch/spot3.lean`, item 6) — and
   `range E ⊆ range v ⊆ span k (v '' C)`.
5. Third conjunct. `span k (range fun a : A ↦ G a) = span k (v '' A₀) = span k (range G)` (step 1 and
   monotonicity), and `span k (range G) = (span P (range h)).restrictScalars k`: `⊆` since
   `monomial ν 1 • h j ∈ span P (range h)`; `⊇` by `Submodule.span_induction` over `P`: the `k`-span of `range G`
   is stable under `p • ·` because `p = ∑ monomial μ (coeff μ p)` (`MvPolynomial.as_sum`) and
   `monomial μ c * monomial ν 1 = monomial (μ + ν) c` (`MvPolynomial.monomial_mul`).
#### Mathlib lemmas needed
`linearIndepOn_empty`, `LinearIndepOn.extend`, `LinearIndepOn.linearIndepOn_extend`, `LinearIndepOn.subset_extend`, `LinearIndepOn.subset_span_extend`, `LinearIndepOn.mono`, `LinearIndepOn.notMem_span_of_insert`, `Pi.basis`, `MvPolynomial.basisMonomials`, `Module.Basis.span_eq`, `Submodule.span_induction`, `MvPolynomial.as_sum`, `MvPolynomial.monomial_mul`, `Submodule.restrictScalars`.
#### Sources
[Bo] 1.3/7 and 1.3/10, `bosch-lectures.txt:896–900`, `:973–978`; decomposition L15.1.
#### Generality decision
A field `k`, any `σ`, a finite `ι`. The choice is of **index sets** (the family `G` may repeat vectors or contain `0`).

### [T063] The monomial vectors are an orthonormal basis of `T^ι`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-2, CLEANUP-21 · **Parallel**: no (same file as T062) · **Type**: theorems
- **Progress**: 2026-10-02T15:53: isOrthonormalBasis_monomial (coefficient formula, crossing the seam by congrArg norm …).trans_le; density via denseRange_toRestricted), isOrthonormalBasis_single_monomial (Pi.nnnorm_single, density through topologicalClosure + continuous_single (A := …)), hasSum_coeff_smul_single_monomial (Pi.hasSum + Injective.hasSum_iff, now without [Fintype ι]); import PrincipalIdealDomain added; std axioms.
- **Leaves**: L15.2–L15.4

#### Statement
```lean
theorem isOrthonormalBasis_monomial :
    IsOrthonormalBasis K fun t : σ →₀ ℕ ↦ (monomial (1 : σ → ℝ) t (1 : K) : 𝕋) := by sorry
theorem isOrthonormalBasis_single_monomial :
    IsOrthonormalBasis K fun p : (Σ _ : ι, σ →₀ ℕ) ↦
      (Pi.single p.1 (monomial (1 : σ → ℝ) p.2 (1 : K)) : ι → 𝕋) := by sorry
theorem hasSum_coeff_smul_single_monomial (f : ι → 𝕋) :
    HasSum (fun p : (Σ _ : ι, σ →₀ ℕ) ↦
      coeff p.2 (f p.1).1 • (Pi.single p.1 (monomial (1 : σ → ℝ) p.2 (1 : K)) : ι → 𝕋)) f := by sorry
```
#### Proof sketch
Private helper in this file (or as a constructor in the proof): to prove the `ℝ≥0` identity of
`IsOrthonormalFamily` it is enough to prove, for every real `C ≥ 0`,
`‖∑ i ∈ s, a i • e i‖ ≤ C ↔ ∀ i ∈ s, ‖a i‖ ≤ C` (then `le_antisymm` with `Finset.sup_le` and
`Finset.le_sup`, using `‖e i‖ = 1`).
1. `isOrthonormalBasis_monomial`.
   - `‖monomial 1 t 1‖ = 1`: `norm_monomial`, `norm_one`, the helper `prod_one_pow` of T004.
   - the coefficient of `∑ t ∈ s, a t • monomial 1 t 1` at `u` is `a u` if `u ∈ s`, else `0`
     (`val_sum`, `val_smul`, `val_monomial`, `MvPowerSeries.coeff_monomial`, `Finset.sum_ite_eq`); the iff is
     then `norm_le_iff_forall_norm_coeff_le`.
   - density: `(denseRange_toRestricted 1).mono`-style: every `toRestricted 1 p` is in the span
     (`MvPolynomial.as_sum`, `map_sum`, `toRestricted_monomial`, `monomial 1 t c = c • monomial 1 t 1`), so the
     span contains a dense set (`Dense.mono`).
2. `isOrthonormalBasis_single_monomial`: `Pi.norm_single` for norm one; the component `i` of
   `∑ p ∈ s, a p • Pi.single p.1 (monomial 1 p.2 1)` is the sum over `p ∈ s` with `p.1 = i`
   (`Finset.sum_apply`, `Pi.smul_apply`, `Pi.single_apply`), so by item 1's computation its coefficient at `u`
   is `a ⟨i, u⟩` if `⟨i, u⟩ ∈ s`, else `0`; `pi_norm_le_iff_of_nonneg` and
   `norm_le_iff_forall_norm_coeff_le`. Density: a tuple is approximated componentwise by tuples of
   polynomials, which lie in the span (`dense_pi`-type argument, or directly with `pi_norm_lt_iff`).
3. `hasSum_coeff_smul_single_monomial`: `Pi.hasSum.2 fun i ↦ ?_`; the `i`-th component of the summand at `p`
   is `monomial 1 p.2 (coeff p.2 (f i).1)` if `p.1 = i`, else `0`;
   `(Function.Injective.hasSum_iff (g := fun t ↦ ⟨i, t⟩) sigma_mk_injective ?_).1 (hasSum_monomial 1 (f i))`,
   the side condition being that the summand vanishes off the fibre over `i`.
#### Mathlib lemmas needed
`Pi.norm_single`, `Pi.hasSum`, `Function.Injective.hasSum_iff`, `sigma_mk_injective`, `pi_norm_le_iff_of_nonneg`, `pi_norm_lt_iff`, `Finset.sum_apply`, `Pi.single_apply`, `MvPowerSeries.coeff_monomial`, `Dense.mono`. Floor: `Restricted.norm_monomial`, `Restricted.hasSum_monomial`, `Restricted.val_sum`, `Restricted.val_monomial`.
#### Sources
[Bo] 1.3/5 and 1.3/10, `bosch-lectures.txt:832–833`, `:981–985`; decomposition L15.2–L15.4.
#### Generality decision
No completeness. The index type of the basis of `T^ι` is `Σ _ : ι, σ →₀ ℕ`, matching `Pi.basis` on the reduction side.

### [T064] The reduction of a submodule
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-5 · **Parallel**: no · **Type**: lemma + definition + theorem
- **Progress**: 2026-10-02T15:53: reductionPi_eq_zero_iff, reductionSubmodule fields, exists_generators_reductionSubmodule (noetherian pi module; fields need import Mathlib.RingTheory.PrincipalIdealDomain for IsNoetherianRing; choose! + equivFin, beta_reduce before rw); std axioms.
- **Leaves**: L15.5–L15.7

#### Statement
```lean
theorem reductionPi_eq_zero_iff {x : ι → 𝕋} (hx : ‖x‖ ≤ 1) : reductionPi x hx = 0 ↔ ‖x‖ < 1 := by sorry
def reductionSubmodule (N : Submodule 𝕋 (ι → 𝕋)) :
    Submodule (MvPolynomial σ 𝕜) (ι → MvPolynomial σ 𝕜) where
  carrier := {u | ∃ (x : ι → 𝕋) (hx : ‖x‖ ≤ 1), x ∈ N ∧ reductionPi x hx = u}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
theorem exists_generators_reductionSubmodule [Finite σ] (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋) (hg : ∀ j, ‖g j‖ = 1), (∀ j, g j ∈ N) ∧
      Submodule.span (MvPolynomial σ 𝕜) (Set.range fun j ↦ reductionPi (g j) (hg j).le) =
        reductionSubmodule N := by sorry
```
#### Proof sketch
1. `reductionPi_eq_zero_iff`: `funext_iff`, `reduction_eq_zero_iff` at each `i`, and
   `pi_norm_lt_iff zero_lt_one`.
2. `reductionSubmodule`, the three fields. `zero_mem'`: `⟨0, by simp, N.zero_mem, by ext; simp [reductionPi]⟩`
   (`map_zero` of `reduction`). `add_mem'`: from `⟨x, hx, hxN, rfl⟩`, `⟨x', hx', hx'N, rfl⟩` take `x + x'`,
   `‖x + x'‖ ≤ max ‖x‖ ‖x'‖ ≤ 1` (the ultrametric instance on `ι → 𝕋` from
   `Mathlib.Topology.MetricSpace.Ultra.Pi`), and componentwise `map_add` of `reduction` (the subtype element
   of a sum is the sum of the subtype elements). `smul_mem'`: for `p` take `P` with `reduction P = p`
   (`reduction_surjective`); `(P : 𝕋) • x ∈ N`, `‖(P : 𝕋) • x‖ ≤ 1` (`pi_norm_le_iff_of_nonneg`,
   `norm_mul_le`, `Subring.norm_le_one`), and componentwise `map_mul`.
3. `exists_generators_reductionSubmodule`: `P := MvPolynomial σ 𝕜` is noetherian
   (`MvPolynomial.isNoetherianRing`, `σ` finite), so `ι → P` is a noetherian module (`isNoetherian_pi`) and
   `reductionSubmodule N` is finitely generated: `obtain ⟨S, hS⟩ := (IsNoetherian.noetherian _)` (a finset
   with span equal to it). `S' := S.erase 0` has the same span. Each `u ∈ S'` is `reductionPi x_u _` with
   `x_u ∈ N`, `‖x_u‖ ≤ 1` (`Submodule.subset_span`, `mem_reductionSubmodule`), and `‖x_u‖ = 1` since `u ≠ 0`
   (item 1). Enumerate `S'` by `S'.equivFin` and choose the lifts (`Classical.choose`); the span of the
   reductions is the span of `S'`.
#### Mathlib lemmas needed
`pi_norm_lt_iff`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `MvPolynomial.isNoetherianRing`, `isNoetherian_pi`, `IsNoetherian.noetherian`, `Submodule.fg_def`, `Finset.equivFin`, `Submodule.span_sdiff_singleton_zero`.
#### Sources
[Bo] 1.3/10, `bosch-lectures.txt:968–973`; decomposition L15.5–L15.7.
#### Generality decision
`[Finite σ]` only in item 3 (`k[X]` must be noetherian). No completeness.

### [CLEANUP-24] Run /cleanup on `TateAlgebra/StrictlyClosed.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: T064 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T15:53: StrictlyClosed.lean (T062–T064 part) runLinter clean, widths ≤ 100.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T065] The adapted family is an orthonormal basis
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-24, CLEANUP-23, CLEANUP-20 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:03: exists_isBald_forall_coeff_mem (closure of the null coefficient family; finite exceptional sets via biUnion of images) and isOrthonormalBasis_adaptedFamily via of_residue_basis (private norm_monomial_one, reduction_monomial_one, norm_adaptedFamily_apply_le, adaptedFamily_reduction; repr transport); std axioms.
- **Leaves**: L15.8, L15.9

#### Statement
```lean
theorem exists_isBald_forall_coeff_mem {r : ℕ} (g : Fin r → ι → 𝕋) (hg : ∀ j, ‖g j‖ ≤ 1) :
    ∃ S : Subring K, S.IsBald ∧ ∀ j i t, coeff t (g j i).1 ∈ S := by sorry
theorem isOrthonormalBasis_adaptedFamily {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hli : LinearIndependent 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B))
    (hspan : Submodule.span 𝕜
      (Set.range (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B)) = ⊤) :
    IsOrthonormalBasis K (adaptedFamily g A B) := by sorry
```
#### Proof sketch
1. `exists_isBald_forall_coeff_mem`: the family
   `a : Fin r × ι × (σ →₀ ℕ) → K := fun q ↦ coeff q.2.2 (g q.1 q.2.1).1`; `‖a q‖ ≤ 1` (`norm_coeff_le`,
   `norm_le_pi_norm`, `hg`); null along the cofinite filter: for `ε > 0` the exceptional set is contained in
   the finite union over `(j, i)` of `{(j, i)} ×ˢ {t | ε ≤ ‖coeff t (g j i).1‖}` (`finite_setOf_le_norm_coeff`,
   `Set.Finite.biUnion`, `Metric.tendsto_nhds` / `Filter.eventually_cofinite`). `Subring.isBald_closure_range`
   and `Subring.subset_closure ⟨_, rfl⟩`.
2. `isOrthonormalBasis_adaptedFamily`: apply `IsOrthonormalBasis.of_residue_basis` (T061) with
   - `x :=` the monomial vectors (`isOrthonormalBasis_single_monomial`);
   - `c μ p := coeff p.2 ((adaptedFamily g A B μ) p.1).1`, so `hy μ := hasSum_coeff_smul_single_monomial _`;
   - `S` from item 1 enlarged by nothing: for `μ = inl a` the coordinates of `monomial 1 ν 1 • g j` are
     coefficients of `g j` or `0` (coefficient of `monomial ν 1 * f` at `t` is `coeff (t - ν) f` if `ν ≤ t`,
     else `0`: `MvPowerSeries.coeff_monomial_mul`), for `μ = inr b` they are `0` or `1`; all in `S`;
   - `r μ := (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ 𝕜).repr
       (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) _) A B μ)`;
   - `hr`: `r μ p = MvPolynomial.coeff p.2 ((reduced adapted family μ) p.1)` (`Pi.basis_repr`,
     `basisMonomials` coordinates are coefficients), and the reduced adapted family is the reduction of the
     adapted family componentwise: for `inl`, `reduction` is multiplicative and
     `reduction ⟨monomial 1 ν 1, _⟩ = monomial ν 1`; for `inr`, `Pi.single`. Then `coeff_reduction`.
   - `hli`, `hspan` for `r`: transport along the linear equivalence `repr` (`LinearIndependent.map'`,
     `Submodule.map_span`, `LinearEquiv.range`).
#### Mathlib lemmas needed
`Set.Finite.biUnion`, `Filter.eventually_cofinite`, `MvPowerSeries.coeff_monomial_mul`, `Pi.basis`, `Pi.basis_repr`, `MvPolynomial.basisMonomials`, `LinearIndependent.map'`, `Submodule.map_span`. Board: `Subring.isBald_closure_range`, `IsOrthonormalBasis.of_residue_basis`.
#### Sources
[Bo] 1.3/10, `bosch-lectures.txt:984–991`; decomposition L15.8, L15.9.
#### Generality decision
No completeness. This ticket is the bridge between the index conventions of the Tate side and of the residue side; expect bookkeeping, not mathematics.

### [T066] Regrouping a series in the multiples `X^ν g_j`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-2 · **Parallel**: no (same file as T062–T065) · **Type**: theorem
- **Progress**: 2026-10-02T16:03: exists_eq_sum_smul_of_hasSum per sketch (u j selects the j-th multiples; squeeze_zero_norm; HasSum.smul_const; Finset.sum_eq_single), no Fintype/DecidableEq needed; std axioms.
- **Leaves**: L15.10

#### Statement
```lean
theorem exists_eq_sum_smul_of_hasSum [CompleteSpace K] {r : ℕ} (g : Fin r → ι → 𝕋)
    {A : Set ((σ →₀ ℕ) × Fin r)} {c : A → K} {a : ι → 𝕋}
    (ha : HasSum (fun μ : A ↦ c μ • (monomial (1 : σ → ℝ) μ.1.1 (1 : K) • g μ.1.2)) a)
    (hc0 : Tendsto c cofinite (𝓝 0)) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ μ, ‖c μ‖ ≤ C) :
    ∃ q : Fin r → 𝕋, (∀ j, ‖q j‖ ≤ C) ∧ a = ∑ j, q j • g j := by sorry
```
#### Proof sketch
For `j : Fin r` let `u j : A → 𝕋 := fun μ ↦ if μ.1.2 = j then c μ • monomial 1 μ.1.1 1 else 0`.
1. `‖u j μ‖ ≤ ‖c μ‖` (`norm_smul_eq`, `norm_monomial`, `norm_one`), so `u j → 0` cofinitely (from `hc0`,
   `squeeze_zero_norm`) and `u j` is summable in the complete ultrametric `𝕋`
   (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`). `q j := ∑' μ, u j μ`.
2. `‖q j‖ ≤ C`: `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun μ ↦ (… ).trans (hC μ)`.
3. `HasSum (fun μ ↦ u j μ • g j) (q j • g j)`: `(hasSum of u j).smul_const (g j)` (`ContinuousSMul 𝕋 (ι → 𝕋)`;
   if the instance is not found, argue componentwise with `Pi.hasSum` and `HasSum.mul_right`).
4. `hasSum_sum` over `j`: `HasSum (fun μ ↦ ∑ j, u j μ • g j) (∑ j, q j • g j)`, and
   `∑ j, u j μ • g j = c μ • (monomial 1 μ.1.1 1 • g μ.1.2)` (`Finset.sum_ite_eq`, `smul_assoc`).
5. `HasSum.unique ha` gives `a = ∑ j, q j • g j`.
#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, `squeeze_zero_norm`, `HasSum.smul_const`, `hasSum_sum`, `HasSum.unique`, `Finset.sum_ite_eq`, `smul_assoc`.
#### Sources
[Bo] 1.3/7, `bosch-lectures.txt:911–914`; decomposition L15.10.
#### Generality decision
`hC0 : 0 ≤ C` (defect D2) and `hc0` (nullity of `c`, supplied by T056 at the call site). `g` is arbitrary here.

### [T067] Elements of `N` have no monomial-vector part
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: T065, T066, T062, T064 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:03: coeff_inr_eq_zero_of_mem via private reductionPi_sum + reductionPi_eq_of_hasSum (reduction of an expansion sees only norm-one coefficients) and disjoint_span_image; exists_isOrthonormalBasis_adaptedFamily assembled as in spot4; import PFA Sums for exists_forall_norm_le; std axioms.
- **Leaves**: L15.11, L15.12

#### Statement
```lean
theorem coeff_inr_eq_zero_of_mem [CompleteSpace K] {N : Submodule 𝕋 (ι → 𝕋)} {r : ℕ}
    {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1) (hgN : ∀ j, g j ∈ N)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hON : IsOrthonormalBasis K (adaptedFamily g A B))
    (hli : LinearIndependent 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B))
    (hA : Submodule.span 𝕜 (Set.range fun a : A ↦
        MvPolynomial.monomial a.1.1 (1 : 𝕜) • reductionPi (g a.1.2) (hg a.1.2).le) =
      (reductionSubmodule N).restrictScalars 𝕜)
    {x : ι → 𝕋} (hx : x ∈ N) {c : A ⊕ B → K}
    (hc : HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) x) (b : B) : c (Sum.inr b) = 0 := by sorry
theorem exists_isOrthonormalBasis_adaptedFamily [Finite σ] [CompleteSpace K]
    (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋) (A : Set ((σ →₀ ℕ) × Fin r)) (B : Set (Σ _ : ι, σ →₀ ℕ)),
      (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧ IsOrthonormalBasis K (adaptedFamily g A B) ∧
        ∀ x ∈ N, ∀ c : A ⊕ B → K, HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) x →
          ∀ b : B, c (Sum.inr b) = 0 := by sorry
```
#### Proof sketch
Write `e := adaptedFamily g A B`, `ẽ := MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) _) A B`.

Private lemma (reduction of an expansion): if `HasSum (fun μ ↦ d μ • e μ) z`, `‖d μ‖ ≤ 1` for all `μ` and
`d → 0`, then `‖z‖ ≤ 1` and `reductionPi z _ = ∑ μ ∈ F, residue _ ⟨d μ, _⟩ • ẽ μ` for the finite set
`F := {μ | ‖d μ‖ = 1}`. Proof: `z - ∑ μ ∈ F, d μ • e μ` is the sum of the remaining terms, all of norm `< 1`,
with a largest one (`Filter.Tendsto.exists_forall_norm_le`), so it has norm `< 1`
(`IsUltrametricDist.norm_tsum_lt_of_forall_lt`, or `hON.1.norm_le_of_hasSum` with that largest value); hence
the two reductions agree (`reductionPi_eq_zero_iff` for the difference, additivity), and the reduction of
`d μ • e μ` is `residue (d μ) • ẽ μ` (`reduction` multiplicative, reduction of a constant, `reductionPi` of
the adapted family as in T065).

1. `coeff_inr_eq_zero_of_mem`. `hc0 := hON.1.tendsto_cofinite_of_hasSum hc`.
   - `A`-part: `x' := ∑' a : A, c (inl a) • e (inl a)` (summable: `hON.1.summable_smul` composed with `inl`);
     by T066 with `C := ‖x‖` (`hON.1.norm_coeff_le_of_hasSum hc`), `x' = ∑ j, q j • g j ∈ N`.
   - `x'' := x - x' ∈ N` has the expansion with coefficients `c'' := fun μ ↦ Sum.elim (fun _ ↦ 0) (c ∘ inr) μ`
     (`HasSum.sub hc` and `Function.Injective.hasSum_iff Sum.inl_injective` for the `A`-part).
   - Suppose `c (inr b) ≠ 0`. Let `b₁` maximise `‖c (inr ·)‖` (`Filter.Tendsto.exists_forall_norm_le` on
     `c ∘ inr`), `d := c (inr b₁) ≠ 0`; `z := d⁻¹ • x'' ∈ N`, with coefficients `d⁻¹ * c''` of norm `≤ 1`, equal
     to `1` at `inr b₁`. By the private lemma, `w := reductionPi z _` is a combination of the `ẽ (inr b)` with
     coefficient `1` at `b₁`, so `w ≠ 0` (`hli`, `linearIndependent_iff'`) and
     `w ∈ span 𝕜 (ẽ '' range inr)`.
   - `w ∈ reductionSubmodule N` (definition), so by `hA`, `w ∈ span 𝕜 (ẽ '' range inl)`.
   - `hli.disjoint_span_image` (ranges of `inl` and `inr` are disjoint) forces `w = 0`. Contradiction.
2. `exists_isOrthonormalBasis_adaptedFamily`: the assembly of `scratch/spot4.lean`, first example, which
   compiles against the skeleton: `exists_generators_reductionSubmodule N`,
   `MvPolynomial.exists_basis_adaptedFamily`, `isOrthonormalBasis_adaptedFamily`, item 1 with
   `hA.trans (by rw [hspan])`.
#### Mathlib lemmas needed
`Function.Injective.hasSum_iff`, `HasSum.sub`, `Sum.inl_injective`, `LinearIndependent.disjoint_span_image`, `linearIndependent_iff'`, `Submodule.disjoint_def`. Chain: `Filter.Tendsto.exists_forall_norm_le`, `IsUltrametricDist.norm_tsum_lt_of_forall_lt`, `IsOrthonormalFamily.summable_smul`, `IsOrthonormalFamily.tendsto_cofinite_of_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`, `IsOrthonormalFamily.norm_le_of_hasSum`.
#### Sources
[Bo] 1.3/7, `bosch-lectures.txt:907–934`; decomposition L15.11, L15.12.
#### Generality decision
`K` complete (the `A`-part must converge and be regrouped). The deepest ticket of the board; the private lemma is the reusable part.

### [CLEANUP-25] Run /cleanup on `TateAlgebra/StrictlyClosed.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: T067 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:03: StrictlyClosed.lean (through T067) runLinter clean, widths ≤ 100; Set.mem_setOf_eq → Set.mem_ofPred_eq.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T068] Generators with a nearest point
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-25 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-02T16:07: exists_generators_forall_exists_isNearest via private exists_sum_smul_hasSum_inr (shared with the refactored T067); std axioms.
- **Leaves**: L15.13

#### Statement
```lean
theorem exists_generators_forall_exists_isNearest (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋), (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ f : ι → 𝕋, ∃ q : Fin r → 𝕋, (∀ j, ‖q j‖ ≤ ‖f‖) ∧
        ∀ a ∈ N, ‖f - ∑ j, q j • g j‖ ≤ ‖f - ∑ j, q j • g j - a‖ := by sorry
```
#### Proof sketch
`classical`; `obtain ⟨r, g, A, B, hgN, hg, hON, hN⟩ := exists_isOrthonormalBasis_adaptedFamily N`;
`refine ⟨r, g, hgN, hg, fun f ↦ ?_⟩`. Let `e := adaptedFamily g A B`.
1. `obtain ⟨c, hc⟩ := hON.exists_hasSum f` (`K` and `ι → 𝕋` complete), `hc0 := hON.1.tendsto_cofinite_of_hasSum hc`,
   `‖c μ‖ ≤ ‖f‖` (`hON.1.norm_coeff_le_of_hasSum hc`).
2. `A`-part: `f_A := ∑' a : A, c (inl a) • e (inl a)`; T066 with `C := ‖f‖` gives `q` with `‖q j‖ ≤ ‖f‖` and
   `f_A = ∑ j, q j • g j`. Use this `q`.
3. `f_B := f - f_A` has the expansion with coefficients `c_B := Sum.elim (fun _ ↦ 0) (c ∘ inr)` (as in T067).
4. For `a ∈ N`: `obtain ⟨d, hd⟩ := hON.exists_hasSum a`, and `d (inr b) = 0` for all `b` (`hN a ha d hd`).
   Then `f_B - a` has coefficients `c_B - d`, equal to `c (inr b)` at `inr b`. So every coefficient of `f_B`
   (namely `0` at `inl`, `c (inr b)` at `inr b`) has norm `≤ ‖f_B - a‖`
   (`hON.1.norm_coeff_le_of_hasSum (hsum of f_B - a)`), and `hON.1.norm_le_of_hasSum (hsum of f_B)
   (norm_nonneg _) _` gives `‖f_B‖ ≤ ‖f_B - a‖`.
#### Mathlib lemmas needed
`HasSum.sub`, `Function.Injective.hasSum_iff`, `Sum.inl_injective`. Chain: `IsOrthonormalBasis.exists_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`, `IsOrthonormalFamily.norm_le_of_hasSum`, `IsOrthonormalFamily.tendsto_cofinite_of_hasSum`.
#### Sources
[Bo] 1.3/9, `bosch-lectures.txt:944–954`; 1.3/10, `:956–993`; decomposition L15.13.
#### Generality decision
One statement from which Bosch 1.3/7–1.3/10 and BGR 5.2.7/8 are read off. `DecidableEq ι` is not in the statement; open `classical`.

### [T069] Submodules of `T^ι` are strictly closed
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: T068 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:07: exists_generators_norm_le, exists_forall_norm_sub_le (sub_sub_sub_cancel_right), isClosed_submodule, infDist_mem_range_norm (Pi.norm_def + exists_mem_eq_sup); std axioms.
- **Leaves**: L15.14–L15.17

#### Statement
```lean
theorem exists_generators_norm_le (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋), (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ x ∈ N, ∃ q : Fin r → 𝕋, x = ∑ j, q j • g j ∧ ∀ j, ‖q j‖ ≤ ‖x‖ := by sorry
theorem exists_forall_norm_sub_le (N : Submodule 𝕋 (ι → 𝕋)) (f : ι → 𝕋) :
    ∃ a₀ ∈ N, ∀ a ∈ N, ‖f - a₀‖ ≤ ‖f - a‖ := by sorry
theorem isClosed_submodule (N : Submodule 𝕋 (ι → 𝕋)) : IsClosed (N : Set (ι → 𝕋)) := by sorry
theorem infDist_mem_range_norm (N : Submodule 𝕋 (ι → 𝕋)) (f : ι → 𝕋) :
    Metric.infDist f (N : Set (ι → 𝕋)) ∈ Set.range (norm : K → ℝ) := by sorry
```
#### Proof sketch
1. `exists_generators_norm_le`: the second example of `scratch/spot4.lean` (compiles): apply T068 to `x ∈ N`;
   the nearest-point inequality at `a := x - ∑ j, q j • g j ∈ N` gives `‖x - ∑ …‖ ≤ 0`.
2. `exists_forall_norm_sub_le`: from T068, `a₀ := ∑ j, q j • g j ∈ N` (`N.sum_mem`, `N.smul_mem`); for
   `a ∈ N` apply the inequality to `a - a₀ ∈ N`: `f - a₀ - (a - a₀) = f - a` (`sub_sub_sub_cancel_right`).
3. `isClosed_submodule`: `isClosed_of_closure_subset fun f hf ↦ ?_`; take `a₀` from item 2;
   `Metric.mem_closure_iff.1 hf ε` gives `a ∈ N` with `dist f a < ε`, so `‖f - a₀‖ < ε` for every `ε > 0`,
   hence `f = a₀ ∈ N` (`le_of_forall_pos_lt_add`-style, `norm_le_zero_iff`, `sub_eq_zero`).
4. `infDist_mem_range_norm`: with `a₀` from item 2, `Metric.infDist f N = ‖f - a₀‖`
   (`le_antisymm (Metric.infDist_le_dist_of_mem a₀.2) ((Metric.le_infDist ⟨0, N.zero_mem⟩).2 _)`,
   `dist_eq_norm`). Then `‖f - a₀‖ ∈ range norm`: `rcases isEmpty_or_nonempty ι`; empty: the norm is `0`
   (`⟨0, norm_zero⟩`); nonempty: `Pi.norm_def`, `Finset.exists_mem_eq_sup` give `i` with
   `‖f - a₀‖ = ‖(f - a₀) i‖`, and `norm_mem_range_norm`.
#### Mathlib lemmas needed
`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.sub_mem`, `isClosed_of_closure_subset`, `Metric.mem_closure_iff`, `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `Pi.norm_def`, `Finset.exists_mem_eq_sup`, `dist_eq_norm`.
#### Sources
[Bo] 1.3/8–10, `bosch-lectures.txt:935–967`; [BGR] 5.2.7/1, 5.2.7/7, 5.2.7/8, `bgr-5.2.md:403–420`, `:486–493`; decomposition L15.14–L15.17.
#### Generality decision
Submodules of a finite free module with the maximum norm. Closedness is read off strict closedness (Bosch sums series instead).

### [CLEANUP-ALL-3] Run /cleanup-all before milestone M3 (T070)
- **Status**: done (2026-10-02) · **Depends on**: T069, CLEANUP-20, CLEANUP-21, CLEANUP-23 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:07: Sweep: Bald, Orthonormal, OrthonormalLift, StrictlyClosed build with only the four T070 sorry warnings, runLinter clean on all, widths ≤ 100, std axioms on the M3 inputs.
- Sweep before the milestone: `Bald.lean`, `PadicFunctionalAnalysis/Orthonormal.lean`, `OrthonormalLift.lean`, `TateAlgebra/StrictlyClosed.lean`. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T070] Ideals of the Tate algebra are strictly closed
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: CLEANUP-ALL-3 · **Parallel**: no · **Type**: theorems (milestone M3) · **Milestone**: M3
- **Progress**: 2026-10-02T16:09: MILESTONE M3: exists_generators_norm_le_ideal, exists_forall_norm_sub_le_ideal, isClosed_ideal, norm_quotient_mk_mem_range_norm via ι := Unit and N := comap (proj ()) I (private norm_unit_pi; calc steps need explicit arguments or whnf times out); quotient norm through QuotientAddGroup.norm_mk; sorry-free, std axioms.
- **Leaves**: L15.18–L15.21

#### Statement
```lean
theorem exists_generators_norm_le_ideal (I : Ideal 𝕋) :
    ∃ (r : ℕ) (g : Fin r → 𝕋), (∀ j, g j ∈ I) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ x ∈ I, ∃ q : Fin r → 𝕋, x = ∑ j, q j * g j ∧ ∀ j, ‖q j‖ ≤ ‖x‖ := by sorry
theorem exists_forall_norm_sub_le_ideal (I : Ideal 𝕋) (f : 𝕋) :
    ∃ a₀ ∈ I, ∀ a ∈ I, ‖f - a₀‖ ≤ ‖f - a‖ := by sorry
theorem isClosed_ideal (I : Ideal 𝕋) : IsClosed (I : Set 𝕋) := by sorry
theorem norm_quotient_mk_mem_range_norm (I : Ideal 𝕋) (f : 𝕋) :
    ‖Ideal.Quotient.mk I f‖ ∈ Set.range (norm : K → ℝ) := by sorry
```
#### Proof sketch
Specialise T069 to `ι := Unit` and `N := Submodule.comap (LinearMap.proj () : (Unit → 𝕋) →ₗ[𝕋] 𝕋) I`
(`x ∈ N ↔ x () ∈ I`); for `x : Unit → 𝕋`, `‖x‖ = ‖x ()‖` (`Pi.norm_def`, `Finset.univ_unique`,
`Finset.sup_singleton`), and `x = fun _ ↦ x ()`.
1. `exists_generators_norm_le_ideal`: from `exists_generators_norm_le N` take `g' j := g j ()`; for `x ∈ I`
   apply it to `fun _ ↦ x` and evaluate at `()` (`Finset.sum_apply`, `Pi.smul_apply`, `smul_eq_mul`).
2. `exists_forall_norm_sub_le_ideal`: from `exists_forall_norm_sub_le N (fun _ ↦ f)`, `a₀ ()`; for `a ∈ I`
   use `fun _ ↦ a`.
3. `isClosed_ideal`: as T069 item 3, from item 2, or the preimage of `isClosed_submodule N`
   under the continuous map `f ↦ fun _ ↦ f`.
4. `norm_quotient_mk_mem_range_norm`: the quotient seminorm is the distance to `I`
   (`QuotientAddGroup.norm_mk`, after unfolding the `Ideal.Quotient` norm instance; `Metric.infDist_eq_iInf`
   if needed); with `a₀` from item 2, the distance is `‖f - a₀‖` as in T069 item 4; `norm_mem_range_norm`.
#### Mathlib lemmas needed
`LinearMap.proj`, `Submodule.comap`, `Pi.norm_def`, `Finset.sup_singleton`, `QuotientAddGroup.norm_mk`, `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `Metric.mem_closure_iff`.
#### Sources
[Bo] 1.3/7–9, `bosch-lectures.txt:885–954`; [BGR] 5.2.7/2, 5.2.7/8, `bgr-5.2.md:418`, `:492–493`; [RM] §0.3.1; decomposition L15.18–L15.21.
#### Generality decision
Milestone M3. `σ` finite, `K` complete. The quotient norm on `𝕋 ⧸ I` is Mathlib's seminorm, defined for every ideal; item 3 makes it a norm.

### [CLEANUP-26] Run /cleanup on `TateAlgebra/StrictlyClosed.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/StrictlyClosed.lean` · **Depends on**: T070 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:09: StrictlyClosed.lean sorry-free, runLinter clean, widths ≤ 100, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T071] Bounded functionals that separate points are all functionals
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Progress**: 2026-10-02T16:14: exists_bound_of_forall_exists_ne_zero via the submodule of bounded functionals and Subspace.dualCoannihilator_dualAnnihilator_eq; std axioms.
- **Leaves**: L16.1

#### Statement
```lean
theorem Module.Dual.exists_bound_of_forall_exists_ne_zero {K : Type*} [NormedField K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : V → ℝ)
    (h : ∀ x : V, x ≠ 0 → ∃ φ : V →ₗ[K] K, (∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y) ∧ φ x ≠ 0)
    (ψ : V →ₗ[K] K) : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C * N y := by sorry
```
#### Proof sketch
`W : Submodule K (Module.Dual K V)` with carrier `{φ | ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y}`:
- `zero_mem'`: `⟨0, fun y ↦ by simp⟩`.
- `add_mem'`: from `C₁`, `C₂` take `C₁ + C₂`: `norm_add_le` and `add_mul` (no sign condition on `N`).
- `smul_mem'`: from `C` take `‖a‖ * C`: `norm_mul`, `mul_assoc`, `mul_le_mul_of_nonneg_left`.
Then `W.dualCoannihilator = ⊥`: `eq_bot_iff`; if `x` is killed by all of `W` and `x ≠ 0`, `h x` gives
`φ ∈ W` with `φ x ≠ 0` (`Submodule.mem_dualCoannihilator`). Hence
`W = W.dualCoannihilator.dualAnnihilator = ⊤` (`Subspace.dualAnnihilator_dualCoannihilator_eq`,
`Submodule.dualAnnihilator_bot`), and `ψ ∈ W`.
#### Mathlib lemmas needed
`Subspace.dualAnnihilator_dualCoannihilator_eq`, `Submodule.dualCoannihilator`, `Submodule.mem_dualCoannihilator`, `Submodule.dualAnnihilator_bot`.
#### Sources
[BGR] 2.3.1/2–3, `bgr-2.md:121–133`; decomposition L16.1.
#### Generality decision
`N : V → ℝ` is an arbitrary function: the proof uses none of its properties. Finite dimension is necessary.

### [T072] The trace is a contraction; separable extensions are weakly cartesian
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: T071 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:14: norm_trace_le_spectralNorm (trace_eq_finrank_mul_minpoly_nextCoeff + le_ciSup on the spectral terms; import Normed.Ring.Ultra) and exists_bound_of_isSeparable (traceForm_nondegenerate.1, spectralNorm_mul without completeness); std axioms.
- **Leaves**: L16.2, L16.3

#### Statement
```lean
theorem norm_trace_le_spectralNorm (x : L) : ‖Algebra.trace K L x‖ ≤ spectralNorm K L x := by sorry
theorem exists_bound_of_isSeparable [Algebra.IsSeparable K L] (φ : L →ₗ[K] K) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by sorry
```
#### Proof sketch
1. `norm_trace_le_spectralNorm`: `q := minpoly K x`, `r := q.natDegree ≥ 1` (`minpoly.natDegree_pos`, `x`
   integral: `Algebra.IsIntegral.isIntegral`).
   `rw [trace_eq_finrank_mul_minpoly_nextCoeff]`: the trace is `(finrank K⟮x⟯ L : K) * -q.nextCoeff`; `norm_mul`,
   `norm_neg`, and `‖(n : K)‖ ≤ 1` (`IsUltrametricDist.norm_natCast_le_one`) reduce to
   `‖q.nextCoeff‖ ≤ spectralNorm K L x`. `Polynomial.nextCoeff_of_natDegree_pos` gives
   `q.nextCoeff = q.coeff (r - 1)`. `spectralNorm K L x = spectralValue q` (definition), and
   `le_ciSup (spectralValueTerms_bddAbove q) (r - 1)` with `spectralValueTerms_of_lt_natDegree`
   (`r - 1 < r`): the term is `‖q.coeff (r - 1)‖ ^ (1 / (r - (r - 1) : ℝ)) = ‖q.coeff (r - 1)‖`
   (`Nat.cast_sub`, `sub_sub_cancel`, `div_one`, `Real.rpow_one`).
2. `exists_bound_of_isSeparable`: `Module.Dual.exists_bound_of_forall_exists_ne_zero (spectralNorm K L) ?_ φ`.
   For `x ≠ 0`: the trace form is nondegenerate (`traceForm_nondegenerate K L`), so there is `y₀` with
   `Algebra.trace K L (x * y₀) ≠ 0`. `φₓ := (Algebra.trace K L).comp (LinearMap.mulRight K y₀)`, bounded by
   `C := spectralNorm K L y₀`: item 1 and `map_mul_le_mul (spectralAlgNorm K L) y y₀`
   (`spectralAlgNorm K L z = spectralNorm K L z` by `rfl`), `mul_comm`.
#### Mathlib lemmas needed
`trace_eq_finrank_mul_minpoly_nextCoeff`, `Polynomial.nextCoeff_of_natDegree_pos`, `minpoly.natDegree_pos`, `IsUltrametricDist.norm_natCast_le_one`, `spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_bddAbove`, `le_ciSup`, `Real.rpow_one`, `traceForm_nondegenerate`, `LinearMap.BilinForm.Nondegenerate`, `spectralAlgNorm`, `map_mul_le_mul`, `LinearMap.mulRight`.
#### Sources
[BGR] 3.2.3/2, `bgr-3.2.md:49–54`; 3.5.1/3, `bgr-3.5.md:57–64`; decomposition L16.2, L16.3.
#### Generality decision
A nonarchimedean normed field, not complete, possibly trivially valued. Ultrametricity is necessary for item 1.

### [T073] Perfect fields and complete fields are weakly stable
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: T072 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:14: isWeaklyStable_of_perfectField, isWeaklyStable_of_completeSpace (LinearMap.toContinuousLinearMap + NormedAlgebra.norm_eq_spectralNorm); std axioms.
- **Leaves**: L16.4, L16.5

#### Statement
```lean
theorem isWeaklyStable_of_perfectField (K : Type u) [NormedField K] [IsUltrametricDist K]
    [PerfectField K] : IsWeaklyStable K := by sorry
theorem isWeaklyStable_of_completeSpace (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : IsWeaklyStable K := by sorry
```
#### Proof sketch
1. `isWeaklyStable_of_perfectField`: `intro L _ _ _ φ`;
   `haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField`;
   `exact exists_bound_of_isSeparable φ`.
2. `isWeaklyStable_of_completeSpace`: `intro L _ _ _ φ`; `letI := spectralNorm.normedField K L`;
   `letI := spectralNorm.normedAlgebra K L`; then `L` is a finite-dimensional normed space over the complete
   field `K`, `φ' := LinearMap.toContinuousLinearMap φ`, and `⟨‖φ'‖, fun y ↦ φ'.le_opNorm y⟩` after
   identifying `‖y‖` with `spectralNorm K L y` (`rfl`, or `(NormedAlgebra.norm_eq_spectralNorm K y)`).
#### Mathlib lemmas needed
`Algebra.IsAlgebraic.isSeparable_of_perfectField`, `spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `LinearMap.toContinuousLinearMap`, `ContinuousLinearMap.le_opNorm`, `NormedAlgebra.norm_eq_spectralNorm`.
#### Sources
[BGR] 3.5.1/4, 3.5.2, `bgr-3.5.md:66–71`, `:80–90`; 2.3.3/4, `bgr-2.md:217–224`; decomposition L16.4, L16.5.
#### Generality decision
Item 2 needs `NontriviallyNormedField` (Mathlib's finite-dimensional continuity). `IsWeaklyStable` quantifies over extensions in the universe of `K`.

### [CLEANUP-27] Run /cleanup on `WeaklyStable.lean`
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: T073 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:14: WeaklyStable.lean (T071–T073) runLinter clean, widths ≤ 100.
- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.

### [T074] The norm of a fraction field
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: CLEANUP-27 · **Parallel**: no (same file as T071–T073) · **Type**: definition + lemmas
- **Progress**: 2026-10-02T16:14: normAbsoluteValue fields via private raw_div and div_add_div_algebraMap (div_surjective representatives); normAbsoluteValue_algebraMap (NormMulClass.toNormOneClass), normAbsoluteValue_div; std axioms.
- **Leaves**: L16.6–L16.8

#### Statement
```lean
noncomputable def normAbsoluteValue (A : Type*) [NormedCommRing A] [NormMulClass A] [Nontrivial A]
    (Q : Type*) [Field Q] [Algebra A Q] [IsFractionRing A Q] : AbsoluteValue Q ℝ where
  toFun q := ‖(IsLocalization.sec (nonZeroDivisors A) q).1‖ /
    ‖((IsLocalization.sec (nonZeroDivisors A) q).2 : A)‖
  map_mul' := by sorry
  nonneg' := by sorry
  eq_zero' := by sorry
  add_le' := by sorry
theorem normAbsoluteValue_algebraMap (a : A) : normAbsoluteValue A Q (algebraMap A Q a) = ‖a‖ := by sorry
theorem normAbsoluteValue_div (a : A) {b : A} (hb : b ≠ 0) :
    normAbsoluteValue A Q (algebraMap A Q a / algebraMap A Q b) = ‖a‖ / ‖b‖ := by sorry
```
#### Proof sketch
`A` is a domain (`NormMulClass.toNoZeroDivisors`, `Nontrivial A`), and `algebraMap A Q` is injective
(`IsFractionRing.injective A Q`).

Private lemma about the raw function `ν q := ‖(IsLocalization.sec (nonZeroDivisors A) q).1‖ /
‖((IsLocalization.sec (nonZeroDivisors A) q).2 : A)‖`:
`ν_div (a) {b} (hb : b ≠ 0) : ν (algebraMap A Q a / algebraMap A Q b) = ‖a‖ / ‖b‖`. Proof:
`IsLocalization.sec_spec` gives `q * algebraMap s = algebraMap r`; with `q = a / b` and injectivity,
`a * s = r * b` in `A`; `norm_mul` twice and `div_eq_div_iff` (`‖s‖ ≠ 0`, `‖b‖ ≠ 0`).

1. `normAbsoluteValue`, the four fields; every `q` is `a / b` (`IsFractionRing.div_surjective`).
   `map_mul'`: `(a / b) * (c / d) = (a * c) / (b * d)` (`div_mul_div_comm`, `map_mul`), `ν_div` three times,
   `norm_mul`. `nonneg'`: `div_nonneg`. `eq_zero'`: `ν (a / b) = 0 ↔ ‖a‖ = 0 ↔ a = 0 ↔ a / b = 0`.
   `add_le'`: `a / b + c / d = (a * d + c * b) / (b * d)` (`div_add_div`), `ν_div`, `norm_add_le`,
   `norm_mul`, and division by `‖b‖ * ‖d‖ > 0`.
2. `normAbsoluteValue_div`: `ν_div`. `normAbsoluteValue_algebraMap`: the case `b = 1` (`map_one`, `div_one`,
   `norm_one` — `NormOneClass A` follows from `NormMulClass` and nontriviality: `norm_one` may need
   `NormMulClass.toNormOneClass`; otherwise use `ν_div a one_ne_zero` and `‖(1 : A)‖ = 1` from
   `‖1‖ * ‖1‖ = ‖1‖`).
#### Mathlib lemmas needed
`IsLocalization.sec`, `IsLocalization.sec_spec`, `IsFractionRing.injective`, `IsFractionRing.div_surjective`, `NormMulClass.toNoZeroDivisors`, `div_eq_div_iff`, `div_mul_div_comm`, `div_add_div`, `norm_mul`.
#### Sources
[BGR] `bgr-3.5.md:143–144` ("the valuation on `K` extends the valuation on `A`"); `bgr-5.2.md:495–497`; decomposition L16.6–L16.8.
#### Generality decision
Any normed commutative ring with multiplicative norm and any model `Q` of its fraction field (`IsFractionRing A Q`). The hypotheses are explicit binders (defect D6).

### [T075] The fraction-field norm is nonarchimedean
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: T074 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-02T16:14: isNonarchimedean_normAbsoluteValue (max_div_div_right, mul_div_mul_right/left), isUltrametricDist; std axioms.
- **Leaves**: L16.9, L16.10

#### Statement
```lean
theorem isNonarchimedean_normAbsoluteValue [IsUltrametricDist A] :
    IsNonarchimedean (normAbsoluteValue A Q) := by sorry
theorem isUltrametricDist [IsUltrametricDist A] :
    letI := normedField A Q
    IsUltrametricDist Q := by sorry
```
#### Proof sketch
1. `isNonarchimedean_normAbsoluteValue`: for `q = a / b`, `q' = c / d`:
   `q + q' = (a * d + c * b) / (b * d)`; `normAbsoluteValue_div`; `‖a * d + c * b‖ ≤ max ‖a * d‖ ‖c * b‖`
   (`IsUltrametricDist.norm_add_le_max`); divide by `‖b‖ * ‖d‖` and simplify each branch of the `max`
   (`max_div_div_right`, `mul_div_mul_right`).
2. `IsFractionRing.isUltrametricDist`: `letI := normedField A Q`;
   `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ isNonarchimedean_normAbsoluteValue A Q x y`
   (the norm of `AbsoluteValue.toNormedField` is the absolute value, by `rfl`).
#### Mathlib lemmas needed
`IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`, `AbsoluteValue.toNormedField`, `max_div_div_right`, `IsNonarchimedean`.
#### Sources
[BGR] `bgr-3.5.md:143–144`; decomposition L16.9, L16.10.
#### Generality decision
`IsFractionRing.normedField` is a reducible definition, not an instance; statements introduce it with `letI`.

### [CLEANUP-28] Run /cleanup on `WeaklyStable.lean`
- **Status**: done (2026-10-02) · **File**: `WeaklyStable.lean` · **Depends on**: T075 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:14: WeaklyStable.lean sorry-free, runLinter clean, widths ≤ 100, std axioms.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T076] Dedekind: perfect fraction field implies Japanese
- **Status**: done (2026-10-02) · **File**: `Japanese.lean` · **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Progress**: 2026-10-02T16:15: isJapaneseRing_of_perfectField: separability from the perfect fraction field, IsIntegralClosure.finite; std axioms.
- **Leaves**: L17.1

#### Statement
```lean
theorem isJapaneseRing_of_perfectField (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [PerfectField (FractionRing A)] :
    IsJapaneseRing A := by sorry
```
#### Proof sketch
`intro L _ _ _ _ _`;
`haveI : Algebra.IsSeparable (FractionRing A) L := Algebra.IsAlgebraic.isSeparable_of_perfectField`;
`exact IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)`.
The instance `IsIntegralClosure (integralClosure A L) A L` is `integralClosure.isIntegralClosure`; the scalar
tower `A → integralClosure A L → L` is the subalgebra's.
#### Mathlib lemmas needed
`IsIntegralClosure.finite`, `integralClosure.isIntegralClosure`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`.
#### Sources
[BGR] 4.2/1, 4.3/1–2, `bgr-4.md:106–119`, `:126–138`; decomposition L17.1.
#### Generality decision
`IsJapaneseRing A` is a `Prop` on the domain, with the extension `L : Type u` given as an algebra over `A` and over `FractionRing A` with a scalar tower.

### [CLEANUP-29] Run /cleanup on `Japanese.lean`
- **Status**: done (2026-10-02) · **File**: `Japanese.lean` · **Depends on**: T076 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:15: Japanese.lean sorry-free, runLinter clean.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [CLEANUP-ALL-4] Run /cleanup-all before milestone M4 (T077)
- **Status**: done (2026-10-02) · **Depends on**: CLEANUP-18, CLEANUP-28, CLEANUP-29 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:16: Sweep: WeaklyStable, Japanese, TateAlgebra/Rueckert build with no warnings (Stable only its two T077 sorries), runLinter clean on all finished modules, std axioms on the M4 inputs.
- Sweep before the milestone: `WeaklyStable.lean`, `Japanese.lean`, `TateAlgebra/Stable.lean`, and the instances of `TateAlgebra/Rueckert.lean` that M4 consumes. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T077] `Q(Tₙ)` is weakly stable and `Tₙ` is Japanese, in characteristic zero
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Stable.lean` · **Depends on**: CLEANUP-ALL-4 · **Parallel**: no · **Type**: theorems (milestone M4) · **Milestone**: M4
- **Progress**: 2026-10-02T16:17: MILESTONE M4: isWeaklyStable_fractionRing (normedField + isUltrametricDist, isWeaklyStable_of_perfectField via PerfectField.ofCharZero) and isJapaneseRing (isJapaneseRing_of_perfectField); sorry-free, std axioms.
- **Leaves**: L18.1, L18.2

#### Statement
```lean
omit [CompleteSpace K] in
theorem isWeaklyStable_fractionRing (n : ℕ) :
    letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
    IsWeaklyStable (FractionRing (TateAlgebra K n)) := by sorry
theorem isJapaneseRing (n : ℕ) : IsJapaneseRing (TateAlgebra K n) := by sorry
```
#### Proof sketch
Both proofs compile against the skeleton (`scratch/spot5.lean`).
1. `isWeaklyStable_fractionRing`:
   `letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))`;
   `haveI := IsFractionRing.isUltrametricDist (TateAlgebra K n) (FractionRing (TateAlgebra K n))`;
   `exact isWeaklyStable_of_perfectField _`. The instances used: `CharZero (TateAlgebra K n)` (T002),
   Mathlib's `IsFractionRing.charZero` and `PerfectField.ofCharZero`, `NormMulClass` and `Nontrivial` on the
   Tate algebra (floor, T002).
2. `isJapaneseRing`: `isJapaneseRing_of_perfectField _`, with `IsDomain` (T002), `IsNoetherianRing` and
   `UniqueFactorizationMonoid` (T050; normality by `inferInstance`).
#### Mathlib lemmas needed
`PerfectField.ofCharZero`, `IsFractionRing.charZero`.
#### Sources
[BGR] 5.3.1/1, 5.3.1/3, `bgr-5.3.1.md:38–41`, `:89–92`; decomposition L18.1, L18.2.
#### Generality decision
Milestone M4. Characteristic zero only: the characteristic-`p` case is BGR 5.3.1/2 with Part A's b-separable modules and is **not on this board** (plan, "Not on this board"). Item 1 holds without completeness of `K` (`omit [CompleteSpace K]`).

### [CLEANUP-30] Run /cleanup on `TateAlgebra/Stable.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Stable.lean` · **Depends on**: T077 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:17: TateAlgebra/Stable.lean sorry-free, runLinter clean.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T078] Examples: variables, a chart, a rational point
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Examples.lean` · **Depends on**: CLEANUP-15, CLEANUP-9 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-10-02T16:23: norm_X, not_isMulDistinguishedX0_X_one (constant coefficient of a unit through Restricted.constantCoeff), isMulDistinguishedX0_shear_X_one (X + C (X 0) Weierstrass), isMaximal_ker_aeval; std axioms.
- **Leaves**: L19.1–L19.4

#### Statement
```lean
theorem norm_X (n : ℕ) (i : Fin n) : ‖Restricted.X K (1 : Fin n → ℝ) i‖ = 1 := by sorry
theorem not_isMulDistinguishedX0_X_one (s : ℕ) :
    ¬ IsMulDistinguishedX0 (Restricted.X K (1 : Fin 2 → ℝ) 1) s := by sorry
theorem isMulDistinguishedX0_shear_X_one :
    IsMulDistinguishedX0 (shear K 1 (fun _ ↦ 1) (Restricted.X K (1 : Fin 2 → ℝ) 1)) 1 := by sorry
theorem isMaximal_ker_aeval {n : ℕ} (x : Fin n → K) (hx : ∀ i, ‖x i‖ ≤ 1) :
    (RingHom.ker (aeval (K := K) (1 : Fin n → ℝ) x hx)).IsMaximal := by sorry
```
#### Proof sketch
1. `norm_X`: `rw [Restricted.norm_X, norm_one, one_mul]; rfl` (the polyradius is `1`).
2. `not_isMulDistinguishedX0_X_one`: `X K 1 1 = ofTail K 1 (X K 1 0)` (`(ofTail_X 0).symm`, `Fin.succ_zero_eq_one`).
   Suppose distinguished of order `s`; `isMulDistinguishedX0_iff` gives `IsUnit (coeffX0 _ s)`, and
   `coeffX0 (ofTail K 1 f) s = (Polynomial.C f).coeff s` (`coeffX0_ofPolynomial`). `s = 0`: the variable of
   `T₁` is not a unit — `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit` (floor) at `t = single 0 1`
   would give `1 < 0`, or use `isUnit_iff` and `coeff 0 (X 0) = 0`. `s > 0`: the coefficient is `0`
   (`Polynomial.coeff_C`), `not_isUnit_zero`.
3. `isMulDistinguishedX0_shear_X_one`: `shear_X_succ (fun _ ↦ 1) 0` and `pow_one` give
   `X 1 + X 0 = ofPolynomial K 1 (Polynomial.X + Polynomial.C (X K 1 0))` (`map_add`, `ofPolynomial_X`,
   `ofTail_X`); `ω := X + C a` is monic of `natDegree 1` (`Polynomial.monic_X_add_C`,
   `Polynomial.natDegree_X_add_C`) with coefficients of norm `≤ 1`, so `isWeierstrassPolynomial_iff` and
   `IsWeierstrassPolynomial.isMulDistinguishedX0`.
4. `isMaximal_ker_aeval`: `haveI : Algebra.IsAlgebraic K K := Algebra.IsAlgebraic.of_finite K K`;
   `exact Affinoid.isMaximal_ker_of_isAlgebraic _`.
#### Mathlib lemmas needed
`Polynomial.monic_X_add_C`, `Polynomial.natDegree_X_add_C`, `Polynomial.coeff_C`, `Fin.succ_zero_eq_one`, `not_isUnit_zero`, `Algebra.IsAlgebraic.of_finite`. Floor: `Restricted.norm_X`, `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit`.
#### Sources
[RM] Layer 0, Examples; [BGR] 5.1.3 Example, 5.2.4; decomposition L19.1–L19.4.
#### Generality decision
The chart example is the variable that is not the distinguished one (the roadmap's `X₁ − X₂` is already distinguished: erratum E12). The generators of the maximal ideal of a rational point are Layer 3.

### [T079] Examples over `ℚ_[p]`: a unit and a reduction
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Examples.lean` · **Depends on**: T078 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-10-02T16:23: norm_one_add_p_mul_X, isUnit_one_add_p_mul_X (isUnit_one_sub_of_norm_lt_one), reduction_p_add_X_add_p_mul_X_sq; private norm_p_lt_one; std axioms.
- **Leaves**: L19.5–L19.7

#### Statement
```lean
theorem norm_one_add_p_mul_X :
    ‖(1 + Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1)‖ = 1 := by sorry
theorem isUnit_one_add_p_mul_X :
    IsUnit (1 + Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1) := by sorry
theorem reduction_p_add_X_add_p_mul_X_sq
    (h : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) + Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 +
      Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 ^ 2 :
        TateAlgebra ℚ_[p] 1)‖ ≤ 1) :
    reduction ⟨Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) + Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 +
      Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 ^ 2,
        mem_unitClosedBall.2 h⟩ = MvPolynomial.X 0 := by sorry
```
#### Proof sketch
`hp : ‖(p : ℚ_[p])‖ < 1`: `Padic.norm_p` and `inv_lt_one_of_one_lt₀` (`1 < (p : ℝ)`, `Nat.Prime.one_lt`).
`hu : ‖C 1 (p : ℚ_[p]) * X ℚ_[p] 1 0‖ < 1`: `norm_mul`, `norm_C`, `norm_X` (T078), `mul_one`.
1. `norm_one_add_p_mul_X`: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (`‖1‖ = 1 ≠ ‖…‖`), `norm_one`,
   `max_eq_left hu.le`.
2. `isUnit_one_add_p_mul_X`: `1 + u = 1 - (-u)` and `isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])`
   (`ℚ_[p]` is complete, so the Tate algebra is).
3. `reduction_p_add_X_add_p_mul_X_sq`: in the subring, the element is
   `⟨C 1 p, _⟩ + ⟨X 0, _⟩ + ⟨C 1 p, _⟩ * ⟨X 0, _⟩ ^ 2` (`Subtype.ext`); `map_add`, `map_mul`, `map_pow`;
   `reduction ⟨C 1 p, _⟩ = 0` by `reduction_eq_zero_iff` (`norm_C`, `hp`); `reduction ⟨X 0, _⟩ = X 0` (the
   coefficientwise lemma of T042, or `MvPolynomial.ext` directly); `zero_add`, `zero_mul`, `add_zero`.
#### Mathlib lemmas needed
`Padic.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.Prime.one_lt`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `isUnit_one_sub_of_norm_lt_one`. Floor: `Restricted.norm_C`.
#### Sources
[RM] Layer 0, Examples; decomposition L19.5–L19.7.
#### Generality decision
`padicNormE.norm_p` no longer exists at the pin; the name is `Padic.norm_p`.

### [T080] Examples over `ℚ_[p]`: a Weierstrass polynomial and a quadratic point
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Examples.lean` · **Depends on**: T079, CLEANUP-13 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-10-02T16:23: isWeierstrassPolynomial_example (simp turns C 1 p into the Nat cast in T, so the bound is stated for (p : T)), isMaximal_span_X_sq_sub_p (mapEquiv to ℚ_[p][X], X² − p has no root by the valuation parity, PID maximality, field transfer along bijective_quotientMap); import Polynomial.SpecificDegree; std axioms.
- **Leaves**: L19.8, L19.9

#### Statement
```lean
theorem isWeierstrassPolynomial_example :
    IsWeierstrassPolynomial ℚ_[p] 1
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) *
        Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0) * Polynomial.X -
          Polynomial.C (Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]))) := by sorry
theorem isMaximal_span_X_sq_sub_p :
    (Ideal.span {ofPolynomial ℚ_[p] 0
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p])))}).IsMaximal := by sorry
```
#### Proof sketch
1. `isWeierstrassPolynomial_example`: `isWeierstrassPolynomial_iff.2 ⟨?_, fun i ↦ ?_⟩`. Monic:
   `X ^ 2 - (C a * X + C b)` with `Polynomial.monic_X_pow_sub` (`degree (C a * X + C b) < 2`,
   `Polynomial.degree_linear_le`), after `sub_sub`. Coefficients: `0`, `1`, `-a`, `-b` with
   `a = C 1 p * X 0`, `b = C 1 p`, of norm `≤ 1` (`norm_neg`, `norm_mul`, `norm_C`, `norm_X`, `Padic.norm_p`);
   compute them with `Polynomial.coeff_sub`, `coeff_X_pow`, `coeff_C_mul_X`, `coeff_C` and a case split on `i`.
2. `isMaximal_span_X_sq_sub_p`. `ω := X ^ 2 - C (C 1 p) : (TateAlgebra ℚ_[p] 0)[X]`.
   - `ω` is a Weierstrass polynomial (as in item 1), so `bijective_quotientMap` (T035) gives a ring
     isomorphism `(TateAlgebra ℚ_[p] 0)[X] ⧸ span {ω} ≃+* TateAlgebra ℚ_[p] 1 ⧸ (span {ω}).map (ofPolynomial _ 0)`
     (`RingEquiv.ofBijective`), and `(span {ω}).map (ofPolynomial _ 0) = span {ofPolynomial _ 0 ω}`
     (`Ideal.map_span`, `Set.image_singleton`).
   - `span {ω}` is maximal: transport along `Polynomial.mapEquiv (Restricted.isEmptyEquiv ℚ_[p] 1)` to
     `span {X ^ 2 - C (p : ℚ_[p])}` in `ℚ_[p][X]` (`Ideal.map_isMaximal_of_equiv` for the inverse,
     `Polynomial.map_sub`, `map_pow`, `map_X`, `map_C`, `isEmptyEquiv` of a constant), which is maximal by
     `PrincipalIdealRing.isMaximal_of_irreducible` once `X ^ 2 - C p` is irreducible:
     `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` (monic of `natDegree 2`) and no root:
     `a ^ 2 = p` would give `‖a‖ ^ 2 = (p : ℝ)⁻¹`, but `‖a‖ = (p : ℝ) ^ (-a.valuation)`
     (`Padic.norm_eq_zpow_neg_valuation`), so `2 * a.valuation = 1` in `ℤ` (`zpow_right_injective₀`), absurd
     (`omega`).
   - a quotient by a maximal ideal is a field; fields transfer along the ring isomorphism
     (`MulEquiv.isField`); `Ideal.Quotient.maximal_of_isField`; rewrite the ideal.
#### Mathlib lemmas needed
`Polynomial.monic_X_pow_sub`, `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`, `PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.map_isMaximal_of_equiv`, `Polynomial.mapEquiv`, `RingEquiv.ofBijective`, `MulEquiv.isField`, `Ideal.Quotient.maximal_of_isField`, `Ideal.map_span`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.norm_p`, `zpow_right_injective₀`.
#### Sources
[RM] Layer 0, Examples (the Weierstrass polynomial `X₂² − pX₁X₂ − p`; a maximal ideal with a quadratic residue field); decomposition L19.8, L19.9.
#### Generality decision
The quadratic point is `(X² − p) ⊂ T₁` over `ℚ_[p]` for every prime `p`, including `p = 2`. The example "`Q(T₁)` is not complete" of the roadmap is not here (erratum E9).

### [CLEANUP-31] Run /cleanup on `TateAlgebra/Examples.lean`
- **Status**: done (2026-10-02) · **File**: `TateAlgebra/Examples.lean` · **Depends on**: T080 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-02T16:23: Examples.lean sorry-free, runLinter clean, widths ≤ 100.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.

### [T081] Add the layer to the chain root
- **Status**: done (2026-10-02) · **File**: `PhD/TauCeti.lean` · **Depends on**: all final per-file cleanups (CLEANUP-2, -5, -7, -8, -9, -10, -12, -13, -15, -17, -18, -20, -21, -23, -26, -28, -29, -30, -31) · **Parallel**: no · **Type**: build
- **Progress**: 2026-10-02T16:24: Appended import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples to PhD/TauCeti.lean (append-only, alphabetical order kept); no sorry in the layer; no PhD.Main import under PhD/TauCeti; lake build PhD.TauCeti passes (3566 jobs, no warnings); #print axioms standard on M1–M4 declarations and ringKrullDim_eq.
- **Leaves**: —

#### Statement
```lean
-- appended to PhD/TauCeti.lean (append-only; another board may be editing the same file)
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples
```
#### Proof sketch
1. `grep -rn "sorry" PhD/TauCeti/Code/RigidAnalyticGeometry PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean`
   must be empty.
2. Append the import line above to `PhD/TauCeti.lean`, keeping the file's ordering convention (re-read the
   file first; do not reorder or remove other boards' lines). `TateAlgebra.Examples` imports every file of
   the board, including `PadicFunctionalAnalysis/Orthonormal.lean`.
3. `lake build PhD.TauCeti` (never `lake build PhD`). Check the CI import rule:
   `grep -rn "import PhD.Main" PhD/TauCeti` is empty.
4. `#print axioms` on the four milestone declarations and on `ringKrullDim_eq`.
#### Mathlib lemmas needed
none.
#### Sources
plan.md, "Build and verification protocol".
#### Generality decision
The root lists leaf modules only.

### [CLEANUP-FINAL] Run /cleanup-all on the whole layer
- **Status**: done (2026-10-05) · **Depends on**: T081 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-05T15:46: Final sweep: lake build PhD.TauCeti passes (3566 jobs, no warnings); runLinter clean on all 41 modules of RigidAnalyticGeometry/ and PadicFunctionalAnalysis/Orthonormal.lean (one combined call OOM-killed at 137, rerun in batches of four); module docstrings list existing names (added the missing one to Restricted/HausdorffDistance.lean); no sorry; std axioms on M1–M4; README Layer 0 status note and memory updated.
- Final sweep of `PhD/TauCeti/Code/RigidAnalyticGeometry/` (skeleton files and the ported floor) and of `PadicFunctionalAnalysis/Orthonormal.lean`: naming, docstrings, import minimality by hand, module docstrings list the final declaration names, `runLinter` clean on every module, `lake build PhD.TauCeti` passes. Then update the Status line of this file, the roadmap README's provenance, and the memory entry of the board.
