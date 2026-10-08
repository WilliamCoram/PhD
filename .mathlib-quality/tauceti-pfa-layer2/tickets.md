# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 2 (the model space and orthonormal bases)

**Board**: `.mathlib-quality/tauceti-pfa-layer2/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and the other `tauceti-*` boards are parallel boards).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 2 (§2.1–§2.7, README l. 585–758) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/{ModelSpace/{Basic,Universal,Reindex,Map,Truncation,Matrix,Dual,Closed,Examples},
Orthogonal,ONable,Serre,CountableType,Unitriangular}.lean` — fourteen files, every declaration already stated with `sorry`
(256 declarations, 262 `sorry`s). Planned 2026-10-06. Status: **APPROVED 2026-10-06 — T001 done at plan review; T002 next.**

## Summary

| | Count |
|---|---|
| Proof / definition / integration tickets | 56 (`T001`–`T056`) |
| Per-file cleanups | 24 (`CLEANUP-1`–`CLEANUP-24`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **86** |

- **Milestone M1** = `T023`: orthonormalisable ⟺ has an orthonormal basis (`Module.isONable_iff_exists_isOrthonormalBasis`) — [RM] §2.2.3.
- **Milestone M2** = `T032`: Serre's theorem over a discretely valued field (`Module.isPotentiallyONable_of_isRankOneDiscrete`,
  `Module.isONable_iff_forall_exists_norm_eq`) — [RM] §2.3.3.
- **Milestone M3** = `T036`: Schneider's Proposition 10.4 (`Module.IsCountableType.exists_continuousLinearEquiv_nat`) — [RM] §2.4.1.
- **Milestone M4** = `T047`: finitely generated submodules of the model space are closed over a Noetherian ring (`isClosed_of_fg`) — [RM] §2.6.5.
- **Milestone M5** = `T051`: the unitriangular-perturbation criterion (`exists_linearIsometryEquiv`, `IsOrthonormalBasis.of_isUnitriangularPerturbation`) — [RM] §2.7.
- Skeleton gate (verified 2026-10-06, 2 688 jobs, 0 errors, one expected linter warning on `toBidual_apply`):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples`.
- `T001` is done (2026-10-06, plan review). Tickets that can start immediately: `T002` (then `T009`, `T014` once CLEANUP-2 lands).

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by `scratch/gen/render.py`. Prove the
   statement as written. If a statement is false or unprovable as stated, that is a **B2 stop** with a concrete counterexample or obstruction —
   never silently change a hypothesis. Private helper lemmas are allowed and expected where a sketch says so; they follow the same conventions.
   Sub-tickets (Tier A) for the long tickets `T030`, `T035`, `T047`, `T050`, `T055` are expected.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited as [SRC] are read-only
   references for proof ideas. Never delete `PhD/PR'd/` or legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` (e.g. `…ModelSpace.Basic`, `…Orthogonal`) — never
   `lake build PhD`. There is no `timeout` binary on this machine: use the tool timeout and check exit codes. Run one Lean process at a time.
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported module, add exactly that module.
5. **Scopes and instances.** `open scoped ContinuousLinearMap.Ultra` activates Layer 1's operator norm; inside `namespace ContinuousLinearMap.Ultra`
   write `Ultra.le_opNorm` when the elaborator complains. The dual example for `ℚ_p` (`T052`) deliberately uses Mathlib's instance. A `def` whose
   proofs are `sorry` currently lacks the instance arguments those proofs will need (plan decision 10): when a signature grows, re-check its users.
6. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows only `propext`,
   `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here (`scratch/gen/mark.py <ID> <status> [progress]`).
7. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with `lake exe runLinter` on the module.
8. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before acting, and delete it only if
   its `BOARD:` line names this board. Other `tauceti-*` boards are parallel; never touch their files.
9. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against the pinned Mathlib
   (`scratch/names*.lean`, five files, ≈ 420 names), except where a sketch says "or …"/"-type" and gives the fallback; Layer 0/1 names are
   marked [L0]/[L1], Newton-polygon names [NP]. `Txxx` refers to an earlier ticket of this board.
10. **Conventions** (plan §"Generality and design decisions"): weakest hypotheses the source allows; commutative scalars only for matrix
    products; explicit bounds and explicit ring arguments; one conclusion per declaration; one-line `Source:` docstrings; readable arithmetic
    (`ring` identity + `mul_le_mul` + `linarith` over `nlinarith`); `omega` not `lia`.
11. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see `plan.md` for the full table)

E19 orthonormal must be `‖∑ aᵢ eᵢ‖ = max ‖aᵢ‖` over rings (torsion counterexample; T001) · E20 family predicates stay root-level, module predicates in
`Module` · E21 linear independence of orthogonal families needs a multiplicative action · E22 dense range of a diagonal operator needs units ·
E23 the value group of `ℂ_p` is not in Mathlib (hypothesis) · E24 §2.4.2's discretely valued orthogonal basis is off the board (no source text) ·
E25 §2.4.3's closed subspaces via Prop 10.5 · E26 `ofBounded` needs an ultrametric complete target, Tate only for the converse · E27 matrix
formulas over commutative rings · E28 the field dual example for Mathlib's norm · E29 the lifting characterisation's universes.

## Dependency order

```text
G0  Orthonormal (shared)  T001 (alone; then rebuild the chain)
G1  Basic                 T002 → {T003 ∥ T004} → CLEANUP-1 → T005 → CLEANUP-2
G2  Universal             CLEANUP-2 → T006 → T007 → T008 → CLEANUP-3
G3  Reindex               CLEANUP-2 → T009 → T010 → T011 → CLEANUP-4 → T012 → CLEANUP-5
G4  Map                   CLEANUP-5 → T013 → CLEANUP-6
G5  Truncation            CLEANUP-2 → T014 → {T015 ∥ T016} → CLEANUP-7
G6  Orthogonal            {T001, CLEANUP-3} → T017 → T018 → T019 → CLEANUP-8 → T020 → CLEANUP-9
G7  ONable                {T020, CLEANUP-5, CLEANUP-7} → T021 → T022 → CLEANUP-ALL-1 → T023 (M1) → CLEANUP-10 → T024 → {T025 ∥ T026} → CLEANUP-11 → T027 → CLEANUP-12
G8  Serre                 CLEANUP-12 → T028 → T029 → T030 → CLEANUP-13 → T031 → CLEANUP-ALL-2 → T032 (M2) → T033 → CLEANUP-14
G9  CountableType         CLEANUP-14 → T034 → T035 → CLEANUP-ALL-3 → T036 (M3) → CLEANUP-15 → T037 → CLEANUP-16
G10 Matrix                {CLEANUP-3, CLEANUP-6} → T038 → T039 → T040 → CLEANUP-17 → T041 → T042 → CLEANUP-18
G11 Dual                  CLEANUP-17 → T043 → T044 → T045 (needs CLEANUP-12) → CLEANUP-19
G12 Closed                {CLEANUP-7, CLEANUP-17} → T046 → CLEANUP-ALL-4 → T047 (M4) → CLEANUP-20
G13 Unitriangular         {CLEANUP-17, CLEANUP-12} → T048 → T049 → T050 → CLEANUP-21 → CLEANUP-ALL-5 → T051 (M5) → CLEANUP-22
G14 Examples              {CLEANUP-16, CLEANUP-19, CLEANUP-20, CLEANUP-22} → T052 → {T053 ∥ T054} → CLEANUP-23 → T055 → CLEANUP-24
Root                      CLEANUP-24 → T056 → CLEANUP-FINAL
```

## Tickets

### [T001] Redefine `IsOrthonormalFamily` (Bellaïche form) and generalise `Orthonormal.lean` to normed rings
- **Status**: done (2026-10-06) · **File**: `Orthonormal.lean` · **Depends on**: none · **Parallel**: yes (edits only the shared file and two RAG files; run alone, then rebuild the chain) · **Type**: definition change + proof repairs
- **Progress**: 2026-10-06 DONE at plan review: definition changed to the Bellaïche form, Orthonormal.lean generalised to normed rings (norm_smul_eq added), three RAG proof sites repaired, chain rebuild pending in the same session
- **Leaves**: L1.1–L1.4

#### Statement
```lean
-- the new second conjunct of `IsOrthonormalFamily` (Orthonormal.lean):
--   ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊
-- all other statements of `Orthonormal.lean` and of the two RAG files are unchanged (only generalised to normed rings).
```
#### Proof sketch
**Files**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean` (shared with the rigid-geometry board, done),
`PhD/TauCeti/Code/RigidAnalyticGeometry/OrthonormalLift.lean` (one proof site, l. 196–198),
`PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/StrictlyClosed.lean` (two proof sites, l. 205–215 and l. 264–278).
Statements of the RAG files are **not** changed; only the three proofs and the one definition.
1. In `Orthonormal.lean` replace the second conjunct of `IsOrthonormalFamily` by
   `∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊` (plan E19); update the two docstrings
   (Source: Bellaïche, Definition II.1.5; Buzzard §2; Colmez, Déf 1.1.3 (ii); roadmap convention 5 as corrected).
2. Generalise the `IsOrthonormalFamily`/`IsOrthonormalBasis` sections from `[NormedField K] [NormedSpace K V]` to
   `{R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]`; `summable_smul` and `exists_hasSum`
   keep `[IsUltrametricDist M] [CompleteSpace M]` and `exists_hasSum` takes `[CompleteSpace R]` instead of
   `[CompleteSpace K]`. Lemma by lemma: `nnnorm_smul_eq` becomes `‖c • e i‖₊ = ‖c‖₊` from the identity at
   `s = {i}` (`Finset.sum_singleton`, `Finset.sup_singleton`); `norm_coeff_le_norm_sum` is the identity plus
   `Finset.le_sup (f := fun j ↦ ‖a j‖₊)`; `norm_sum_le` is the identity plus `Finset.sup_le`; `linearIndependent`,
   `norm_coeff_le_of_hasSum`, `norm_le_of_hasSum`, `eq_of_hasSum` keep their proofs; `tendsto_cofinite_of_hasSum`
   and `summable_smul` replace `norm_smul, he.1, mul_one` by the new `nnnorm_smul_eq`/its real form;
   `exists_hasSum` is unchanged except for the instance (its Cauchy argument runs in `R`).
3. `OrthonormalLift.lean:196`: the final `refine ⟨hy1, fun s a ↦ le_antisymm (Finset.nnnorm_sum_le_sup_nnnorm s _)
   (Finset.sup_le fun μ hμ ↦ ?_)⟩` now has goals `‖∑‖₊ ≤ s.sup ‖a μ‖₊` and `‖a μ‖₊ ≤ ‖∑‖₊`: for the first
   compose `Finset.nnnorm_sum_le_sup_nnnorm` with `Finset.sup_mono_fun fun μ _ ↦ by rw [nnnorm_smul, …hy1…, mul_one]`
   (`‖a μ • y μ‖₊ = ‖a μ‖₊`); for the second drop the `norm_smul, hy1, mul_one` rewrite and use `hkey s a μ hμ`.
4. `StrictlyClosed.lean:205` and `:264`: in the first bullet of each, the `hu` branch uses
   `Finset.le_sup (f := fun t ↦ ‖a t‖₊) hu` directly (no `← hsmul`); in the second bullet drop `rw [hsmul, …]`
   and keep the `coe_nnnorm` conversion; delete `hsmul` if it becomes unused.
5. Rebuild the dependents: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples` and
   `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples` (or the whole chain `lake build PhD.TauCeti`),
   then `lake exe runLinter PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal`.

#### Mathlib lemmas needed
`Finset.sum_singleton`, `Finset.sup_singleton`, `Finset.le_sup`, `Finset.sup_le`, `Finset.sup_mono_fun`, `Finset.nnnorm_sum_le_sup_nnnorm`, `nnnorm_smul`, `NNReal.coe_le_coe`, `coe_nnnorm`, `cauchySeq_tendsto_of_complete`.
#### Sources
[Bel] Def II.1.5 l. 2010–2015 ("`|m| = sup_i |a_i|`"); [Buz07] l. 229–236; [Col] Déf 1.1.3 (ii) l. 108–109; E19 (plan) with the torsion counterexample; [RAG] the three proof sites.
#### Generality decision
Normed-ring scalars everywhere; the field lemmas are instances. **Seam S1**: the only ticket touching files outside this board's new files; run it first and alone.

### [T002] The sup norm on `C₀(I, E)`
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: none · **Parallel**: yes (parallel with T001) · **Type**: lemmas
- **Leaves**: L2.1–L2.7

#### Statement
```lean
theorem norm_eq_iSup (f : C₀(I, E)) : ‖f‖ = ⨆ i, ‖f i‖ := by
  sorry

theorem norm_apply_le (f : C₀(I, E)) (i : I) : ‖f i‖ ≤ ‖f‖ := by
  sorry

theorem norm_le_of_forall_le {f : C₀(I, E)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  sorry

theorem sum_apply {ι : Type*} (s : Finset ι) (F : ι → C₀(I, E)) (i : I) :
    (∑ j ∈ s, F j) i = ∑ j ∈ s, F j i := by
  sorry

theorem tendsto_cofinite (f : C₀(I, E)) : Tendsto f cofinite (𝓝 0) := by
  sorry

theorem exists_norm_apply_eq_norm [Nonempty I] (f : C₀(I, E)) : ∃ i, ‖f i‖ = ‖f‖ := by
  sorry

theorem countable_support {I E : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [SeminormedAddCommGroup E] (f : C₀(I, E)) : {i | f i ≠ 0}.Countable := by
  sorry
```
#### Proof sketch
1. `norm_eq_iSup`: `rw [← norm_toBCF_eq_norm, BoundedContinuousFunction.norm_eq_iSup_norm]; rfl` (`toBCF_apply`).
2. `norm_apply_le`: `rw [← norm_toBCF_eq_norm]; exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF i`.
3. `norm_le_of_forall_le`: `rw [← norm_toBCF_eq_norm]; exact (BoundedContinuousFunction.norm_le hC).2 h`.
4. `sum_apply`: `Finset.cons_induction` with `Finset.sum_cons` and `add_apply` (there is no `coeFnAddMonoidHom` for `C₀`).
5. `tendsto_cofinite`: `have := f.zero_at_infty'; rwa [cocompact_eq_cofinite] at this`.
6. `exists_norm_apply_eq_norm`: `obtain ⟨i, hi⟩ := (tendsto_cofinite f).exists_norm_eq_iSup` (Layer 0 `Sums.lean`), then `⟨i, by rw [hi, norm_eq_iSup]⟩`.
7. `countable_support`: `{i | f i ≠ 0} = ⋃ n : ℕ, {i | (n + 1 : ℝ)⁻¹ < ‖f i‖}` (`Set.ext`, `norm_pos_iff`, `exists_nat_one_div_lt`);
   each set is finite by `Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1 (tendsto_cofinite f) _ (by positivity))`
   (complement form, `dist_zero_right`), so `Set.countable_iUnion fun n ↦ (…).countable`.

#### Mathlib lemmas needed
`ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`, `toBCF_apply`, `BoundedContinuousFunction.{norm_eq_iSup_norm, norm_coe_le_norm, norm_le}`, `Finset.cons_induction`, `Finset.sum_cons`, `ZeroAtInftyContinuousMap.add_apply`, `cocompact_eq_cofinite`, `Filter.Tendsto.exists_norm_eq_iSup` [L0], `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.countable_iUnion`, `Set.Finite.countable`, `exists_nat_one_div_lt`, `norm_pos_iff`.
#### Sources
[RM] §2.1.1 ("the sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`, that the supremum is attained when `f ≠ 0`, that `f → 0` cofinitely"); [Sch] §3 l. 495–520 (`c₀(X)`), the dual example l. 617–700 ("each `Y_x` is finite or countable").
#### Generality decision
Any topological `I` for L2.1–L2.4 (the formula is Mathlib's for `α →ᵇ β`); `DiscreteTopology I` only from L2.5 on; seminormed `E` throughout.

### [T003] The instances Mathlib lacks on `C₀(I, E)`
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: T002 · **Parallel**: no · **Type**: instances
- **Leaves**: L3.1–L3.3

#### Statement
```lean
instance instIsUltrametricDist [IsUltrametricDist E] : IsUltrametricDist C₀(I, E) := by
  sorry

instance instIsBoundedSMul : IsBoundedSMul R C₀(I, E) := by
  sorry

instance instNormSMulClass [NormSMulClass R E] : NormSMulClass R C₀(I, E) := by
  sorry
```
#### Proof sketch
1. `instIsUltrametricDist`: `⟨fun f g h ↦ ?_⟩` with the field `dist_triangle_max`; rewrite the three distances with
   `dist_eq_norm`; `norm_le_of_forall_le (le_max_of_le_left dist_nonneg) fun i ↦ ?_`; `(f - h) i = (f - g) i + (g - h) i`
   (`sub_apply`, `sub_add_sub_cancel`), then `IsUltrametricDist.norm_add_le_max` and `max_le_max (norm_apply_le _ i) (norm_apply_le _ i)`.
2. `instIsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le fun r f ↦ norm_le_of_forall_le (mul_nonneg (norm_nonneg r) (norm_nonneg f))
   fun i ↦ by rw [smul_apply]; exact (norm_smul_le r (f i)).trans (mul_le_mul_of_nonneg_left (norm_apply_le f i) (norm_nonneg r))`.
3. `instNormSMulClass`: `⟨fun r f ↦ by simp_rw [norm_eq_iSup, smul_apply, norm_smul, Real.mul_iSup_of_nonneg (norm_nonneg r)]⟩`.

#### Mathlib lemmas needed
`IsUltrametricDist.mk` (field `dist_triangle_max`), `dist_eq_norm`, `IsUltrametricDist.norm_add_le_max`, `max_le_max`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul_le`, `ZeroAtInftyContinuousMap.smul_apply`, `norm_smul`, `Real.mul_iSup_of_nonneg`.
#### Sources
[RM] §2.1.1 ("Add to `C₀(I, E)` … the instances Mathlib lacks: `IsUltrametricDist`, and … `IsBoundedSMul R C₀(I, E)` (and `NormSMulClass` when `E` has it)").
#### Generality decision
Any topological `I`; `[SeminormedRing R] [Module R E] [IsBoundedSMul R E]` for the action (the `Module R C₀(I, E)` instance is Mathlib's, through `ContinuousConstSMul`).

### [T004] The coordinate vectors `single i x`
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: T002 · **Parallel**: yes (parallel with T003) · **Type**: definition + lemmas
- **Leaves**: L4.1–L4.6

#### Statement
```lean
def single (i : I) (x : E) : C₀(I, E) :=
  ofTendsto (Pi.single i x) (by sorry)

theorem single_apply_self (i : I) (x : E) : single i x i = x := by
  sorry

theorem single_apply_of_ne {i j : I} (h : j ≠ i) (x : E) : single i x j = 0 := by
  sorry

@[simp]
theorem single_zero (i : I) : single i (0 : E) = 0 := by
  sorry

@[simp]
theorem norm_single (i : I) (x : E) : ‖single i x‖ = ‖x‖ := by
  sorry

theorem smul_single {R : Type*} [SeminormedRing R] [Module R E] [IsBoundedSMul R E] (r : R)
    (i : I) (x : E) : r • single i x = single i (r • x) := by
  sorry
```
#### Proof sketch
1. The `sorry` in `single`: `Tendsto (Pi.single i x) cofinite (𝓝 0)` is
   `tendsto_const_nhds.congr' (Filter.eventually_cofinite.2 ((Set.finite_singleton i).subset fun j hj ↦ by_contra fun h ↦ hj (Pi.single_eq_of_ne h x)))`
   (the set where `Pi.single i x j ≠ 0` is inside `{i}`).
2. `single_apply_self`: `Pi.single_eq_same`; `single_apply_of_ne`: `Pi.single_eq_of_ne h`.
3. `single_zero`: `ext j; simp [Pi.single_zero]`.
4. `norm_single`: `le_antisymm (norm_le_of_forall_le (norm_nonneg x) fun j ↦ ?_) ?_`; upper: `by_cases hj : j = i` with
   `Pi.single_eq_same`/`Pi.single_eq_of_ne` and `norm_zero`; lower: `(single_apply_self i x) ▸ norm_apply_le (single i x) i`.
5. `smul_single`: `ext j; rw [smul_apply, coe_single, coe_single, ← Pi.single_smul]`.

#### Mathlib lemmas needed
`tendsto_const_nhds`, `Filter.Tendsto.congr'`, `Filter.eventually_cofinite`, `Set.finite_singleton`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `Pi.single_zero`, `Pi.single_smul`, `norm_zero`.
#### Sources
[RM] §2.1.2 ("The coordinate vectors `single i r`"); [Sch] §3 ("`1_x`"); [Buz07] l. 238–243 ("`e_i` … the function sending `j` to `0` if `i ≠ j`, and to `1` if `i = j`").
#### Generality decision
`single` is stated for any seminormed `E` (used with `E = R` and, in `IsONable.zeroAtInfty`, with `E = M`); `[DecidableEq I]` because it is `Pi.single`.

### [CLEANUP-1] Run `/cleanup` on `ModelSpace/Basic.lean`
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: T002, T003, T004 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Basic.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T005] The coordinate expansion and the density of finitely supported families
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: CLEANUP-1 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L5.1–L5.5

#### Statement
```lean
theorem hasSum_single_apply (f : C₀(I, E)) : HasSum (fun i ↦ single i (f i)) f := by
  sorry

theorem dense_span_range_single (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E] :
    Dense (Submodule.span R (Set.range fun p : I × E ↦ single p.1 p.2) : Set C₀(I, E)) := by
  sorry

theorem hasSum_smul_single_one (f : C₀(I, R)) : HasSum (fun i ↦ f i • single i (1 : R)) f := by
  sorry

theorem dense_span_range_single_one :
    Dense (Submodule.span R (Set.range fun i : I ↦ single i (1 : R)) : Set C₀(I, R)) := by
  sorry

theorem norm_evalCLM [NormOneClass R] (i : I) : ‖(evalCLM R i : C₀(I, R) →L[R] R)‖ = 1 := by
  sorry
```
#### Proof sketch
1. `hasSum_single_apply`: `HasSum` is `Tendsto (fun s : Finset I ↦ ∑ i ∈ s, single i (f i)) atTop (𝓝 f)`; use `Metric.tendsto_atTop.2 fun ε hε ↦ ?_`.
   From `Metric.tendsto_nhds.1 (tendsto_cofinite f) (ε / 2) (half_pos hε)` and `Filter.eventually_cofinite` the set
   `B := {i | ¬ ‖f i‖ < ε / 2}` is finite; take `N := B.toFinset`. For `s ≥ N`: pointwise
   `(∑ i ∈ s, single i (f i)) j = if j ∈ s then f j else 0` (`sum_apply`, `coe_single`, `Finset.sum_pi_single'`), so
   `‖(f - ∑ …) j‖ = if j ∈ s then 0 else ‖f j‖ ≤ ε / 2` (`j ∉ s ⟹ j ∉ B`), hence `dist (∑ …) f ≤ ε / 2 < ε` via
   `dist_eq_norm'`/`norm_le_of_forall_le`.
2. `dense_span_range_single`: `Metric.dense_iff`/`Metric.mem_closure_iff`: for `f` and `ε`, the partial sum
   `∑ i ∈ N, single i (f i)` lies in the span (`Submodule.sum_mem`, `Submodule.subset_span ⟨(i, f i), rfl⟩`) and is within
   `ε` by the tendsto of step 1 (`Metric.tendsto_atTop.1`).
3. `hasSum_smul_single_one`: `(hasSum_single_apply f).congr?` — show `f i • single i 1 = single i (f i)` by
   `smul_single, smul_eq_mul, mul_one` and rewrite (`funext`, `simpa only`).
4. `dense_span_range_single_one`: as 2 with `f i • single i 1` (`Submodule.smul_mem`), or from 2 with
   `Submodule.span_le`-monotonicity (`single i x = x • single i 1`) and `Dense.mono`.
5. `norm_evalCLM`: `le_antisymm (opNorm_le_bound _ zero_le_one fun f ↦ by rw [one_mul]; exact norm_apply_le f i) ?_`;
   lower: `have h := le_opNorm_of_bound (evalCLM R i) ⟨1, fun f ↦ by rw [one_mul]; exact norm_apply_le f i⟩ (single i 1)`,
   then `rw [evalCLM_apply, single_apply_self, norm_one, norm_single, norm_one, mul_one] at h`.

#### Mathlib lemmas needed
`Metric.tendsto_atTop`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.toFinset`, `Finset.sum_pi_single'`, `dist_eq_norm'`, `Metric.mem_closure_iff`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`, `Dense.mono`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound}` [L1], `norm_one`.
#### Sources
[RM] §2.1.2 ("the coordinate functionals `eval i : C₀(I, R) →L[R] R` of norm `1`, and the expansion `f = ∑' i, f i • single i 1`, convergent in norm; finitely supported families are dense"); [Bel] footnote l. 2022–2027 (the convergence of `∑ m_i` along finite subsets); [Buz07] l. 243–245 ("the `e_i` are an ON basis for `c_A(I)`").
#### Generality decision
No completeness and no ultrametricity: the partial sums are truncations and converge for any seminormed `E` (plan decision 8). `norm_evalCLM` needs `[NormOneClass R]` (`‖single i 1‖ = ‖1‖`) and no Tate hypothesis (`le_opNorm_of_bound`).

### [CLEANUP-2] Run `/cleanup` on `ModelSpace/Basic.lean`
- **Status**: open · **File**: `ModelSpace/Basic.lean` · **Depends on**: T005 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Basic.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T006] Uniqueness: a map out of the model space is determined on the coordinate vectors
- **Status**: open · **File**: `ModelSpace/Universal.lean` · **Depends on**: CLEANUP-2 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L6.1–L6.3

#### Statement
```lean
theorem hasSum_smul_apply_single (u : C₀(I, R) →L[R] M) (f : C₀(I, R)) :
    HasSum (fun i ↦ f i • u (single i 1)) (u f) := by
  sorry

theorem ext_single {u v : C₀(I, R) →L[R] M} (h : ∀ i, u (single i 1) = v (single i 1)) : u = v := by
  sorry

theorem exists_bound_single [NormOneClass R] [IsTate R] (u : C₀(I, R) →L[R] M) :
    ∃ C, ∀ i, ‖u (single i 1)‖ ≤ C := by
  sorry
```
#### Proof sketch
1. `hasSum_smul_apply_single`: `have h := (hasSum_smul_single_one f).mapL u` gives `HasSum (fun i ↦ u (f i • single i 1)) (u f)`;
   `simpa only [map_smul] using h`.
2. `ext_single`: `ContinuousLinearMap.ext fun f ↦ (hasSum_smul_apply_single u f).unique (by simpa only [h] using hasSum_smul_apply_single v f)`.
3. `exists_bound_single`: `⟨‖u‖, fun i ↦ by simpa [norm_single, norm_one] using le_opNorm u (single i 1)⟩` (`[IsTate R]`, `[NormOneClass R]`).

#### Mathlib lemmas needed
`HasSum.mapL`, `ContinuousLinearMap.map_smul`, `HasSum.unique`, `ContinuousLinearMap.ext`, `ContinuousLinearMap.Ultra.le_opNorm` [L1], `norm_single`, `norm_one`.
#### Sources
[Sch] universal property of `c₀(X)` l. 2905–2947 ("`f` is uniquely determined by its values on the `1_x`"); [Buz07] l. 274–280 ("if `φ` is continuous and `φ(e_i) = n_i`, then the `n_i` are a bounded collection of elements of `N` which uniquely determine `φ`").
#### Generality decision
L6.1–L6.2 over any normed ring and any normed module (no completeness); L6.3 is the only Tate-dependent fact (plan E26).

### [T007] The universal property: `ofBounded`
- **Status**: open · **File**: `ModelSpace/Universal.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L7.1–L7.5

#### Statement
```lean
theorem summable_smul_of_bounded (f : C₀(I, R)) (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    Summable fun i ↦ f i • m i := by
  sorry

theorem norm_tsum_smul_le (f : C₀(I, R)) (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖∑' i, f i • m i‖ ≤ (⨆ i, ‖m i‖) * ‖f‖ := by
  sorry

noncomputable def ofBounded (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) : C₀(I, R) →L[R] M :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∑' i, f i • m i
      map_add' := by sorry
      map_smul' := by sorry }
    (⨆ i, ‖m i‖) (fun f ↦ norm_tsum_smul_le f m hm)

theorem hasSum_ofBounded (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (f : C₀(I, R)) :
    HasSum (fun i ↦ f i • m i) (ofBounded R m hm f) := by
  sorry

theorem norm_ofBounded_le (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖ofBounded R m hm‖ ≤ ⨆ i, ‖m i‖ := by
  sorry
```
#### Proof sketch
1. `summable_smul_of_bounded`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` (the `NonarchimedeanAddGroup M` instance comes
   from `IsUltrametricDist M`); the family tends to `0`: `tendsto_zero_iff_norm_tendsto_zero` and `squeeze_zero` with
   `‖f i • m i‖ ≤ ‖f i‖ * max C 0` (`norm_smul_le`, `hm.choose_spec`) and `((tendsto_cofinite f).norm.mul_const _)` (`norm_zero`, `zero_mul`).
2. `norm_tsum_smul_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le (mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg f)) fun i ↦ ?_`;
   `‖f i • m i‖ ≤ ‖f i‖ * ‖m i‖ ≤ ‖f‖ * ⨆ j, ‖m j‖` by `norm_smul_le`, `mul_le_mul (norm_apply_le f i) (le_ciSup ⟨C, …⟩ i) …`, `mul_comm`
   (`BddAbove (Set.range fun i ↦ ‖m i‖)` from `hm`: `⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩`).
3. `ofBounded`'s `map_add'`: `simp_rw [add_apply, add_smul]; exact (summable_smul_of_bounded f m hm).tsum_add (summable_smul_of_bounded g m hm)`;
   `map_smul'`: `simp_rw [smul_apply, smul_eq_mul, mul_smul]; exact ((summable_smul_of_bounded f m hm).tsum_const_smul r).symm` (`RingHom.id_apply`).
4. `hasSum_ofBounded`: `(summable_smul_of_bounded f m hm).hasSum`.
5. `norm_ofBounded_le`: `opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_ofBounded_apply_le m hm)`.

#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_zero_iff_norm_tendsto_zero`, `squeeze_zero`, `Filter.Tendsto.mul_const`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `le_ciSup`, `Real.iSup_nonneg`, `Summable.tsum_add`, `Summable.tsum_const_smul`, `Summable.hasSum`, `ContinuousLinearMap.Ultra.opNorm_le_bound` [L1].
#### Sources
[RM] §2.1.3 ("bounded families `I → M` correspond to continuous linear maps `C₀(I, R) →L[R] M` by `m ↦ (f ↦ ∑' i, f i • m i)`, with `‖u‖ = sup ‖m i‖`"); [Sch] l. 2905–2947 ("for any map `x ↦ v_x` into a bounded subset of `V` there is a unique continuous linear map `f : c₀(X) → V` with `f(1_x) = v_x`"); [Buz07] l. 280–283.
#### Generality decision
`M` ultrametric and complete, `R` any normed ring (plan E26); the ring is explicit (`ofBounded R m hm`) because nothing else determines it.

### [T008] `ofBounded` on the coordinate vectors, its norm, and the converse
- **Status**: open · **File**: `ModelSpace/Universal.lean` · **Depends on**: T007 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L8.1–L8.3

#### Statement
```lean
@[simp]
theorem ofBounded_single (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (i : I) :
    ofBounded R m hm (single i (1 : R)) = m i := by
  sorry

theorem norm_ofBounded [NormOneClass R] (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖ofBounded R m hm‖ = ⨆ i, ‖m i‖ := by
  sorry

theorem eq_ofBounded [NormOneClass R] [IsTate R] (u : C₀(I, R) →L[R] M) :
    u = ofBounded R (fun i ↦ u (single i 1)) (exists_bound_single u) := by
  sorry
```
#### Proof sketch
1. `ofBounded_single`: `rw [ofBounded_apply, tsum_eq_single i (fun j hj ↦ by rw [single_apply_of_ne hj, zero_smul]), single_apply_self, one_smul]`.
2. `norm_ofBounded`: `le_antisymm (norm_ofBounded_le R m hm) (Real.iSup_le (fun i ↦ ?_) (opNorm_nonneg _))`; for each `i`:
   `have h := le_opNorm_of_bound (ofBounded R m hm) ⟨_, norm_ofBounded_apply_le m hm⟩ (single i 1)`, then
   `rw [ofBounded_single, norm_single, norm_one, mul_one] at h`.
3. `eq_ofBounded`: `ext_single fun i ↦ (ofBounded_single _ _ i).symm`.

#### Mathlib lemmas needed
`tsum_eq_single`, `zero_smul`, `one_smul`, `Real.iSup_le`, `ContinuousLinearMap.Ultra.{le_opNorm_of_bound, opNorm_nonneg}` [L1], `norm_single`, `norm_one`.
#### Sources
[RM] §2.1.3 ("with `‖u‖ = sup ‖m i‖`"); [Sch] l. 2905–2947 ("`f(1_x) = v_x`"); [Buz07] l. 280–283 ("there is a unique continuous map `φ : M → N` such that `φ(e_i) = n_i` for all `i`, and `|φ| = sup_{i∈I} |n_i|`").
#### Generality decision
`norm_ofBounded` needs `[NormOneClass R]`, no Tate hypothesis; `eq_ofBounded` needs `[IsTate R]` only through `exists_bound_single`.

### [CLEANUP-3] Run `/cleanup` on `ModelSpace/Universal.lean`
- **Status**: open · **File**: `ModelSpace/Universal.lean` · **Depends on**: T008 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Universal.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T009] Reindexing along a bijection
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (parallel with T006–T008) · **Type**: definition + lemma
- **Leaves**: L9.1–L9.2

#### Statement
```lean
noncomputable def reindex (e : I ≃ J) : C₀(I, E) ≃ₗᵢ[R] C₀(J, E) where
  toFun f := ofTendsto (fun j ↦ f (e.symm j)) (by sorry)
  invFun g := ofTendsto (fun i ↦ g (e i)) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

theorem reindex_single [DecidableEq I] [DecidableEq J] (e : I ≃ J) (i : I) (x : E) :
    reindex (R := R) e (single i x) = single (e i) x := by
  sorry
```
#### Proof sketch
1. The two `tendsto` fields: `(tendsto_cofinite f).comp e.symm.injective.tendsto_cofinite` and `(tendsto_cofinite g).comp e.injective.tendsto_cofinite`.
2. `map_add'`, `map_smul'`: `ext; rfl`. `left_inv`/`right_inv`: `fun f ↦ by ext; simp` (`Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`).
3. `norm_map'`: `le_antisymm` with `norm_le_of_forall_le (norm_nonneg _)` in both directions and `norm_apply_le` (every value of
   `f ∘ e.symm` is a value of `f` and conversely), avoiding `iSup` lemmas.
4. `reindex_single`: `ext j; simp only [reindex_apply, coe_single, Pi.single_apply, Equiv.symm_apply_eq]`.

#### Mathlib lemmas needed
`Function.Injective.tendsto_cofinite`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`, `Equiv.symm_apply_eq`, `Pi.single_apply`.
#### Sources
[RM] §2.1.4 ("A bijection `I ≃ J` induces an isometry `C₀(I, R) ≃ₗᵢ[R] C₀(J, R)`").
#### Generality decision
Values in any normed module `E` over a normed ring (used with `E = R` and `E = M`).

### [T010] Disjoint unions and products of index sets
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: definitions
- **Leaves**: L10.1–L10.2

#### Statement
```lean
noncomputable def sumEquiv : C₀(I ⊕ J, E) ≃ₗᵢ[R] C₀(I, E) × C₀(J, E) where
  toFun f := (ofTendsto (fun i ↦ f (Sum.inl i)) (by sorry), ofTendsto (fun j ↦ f (Sum.inr j)) (by sorry))
  invFun p := ofTendsto (Sum.elim p.1 p.2) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

noncomputable def prodEquiv : C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E)) where
  toFun f := ofTendsto (fun i ↦ ofTendsto (fun j ↦ f (i, j)) (by sorry)) (by sorry)
  invFun g := ofTendsto (fun p ↦ g p.1 p.2) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry
```
#### Proof sketch
1. `sumEquiv`: the two tendsto fields of `toFun` are `(tendsto_cofinite f).comp Sum.inl_injective.tendsto_cofinite` (resp. `inr`); for `invFun`,
   `Tendsto (Sum.elim p.1 p.2) cofinite (𝓝 0)`: by `Metric.tendsto_nhds` and `Filter.eventually_cofinite`, the bad set is
   `Sum.inl '' B₁ ∪ Sum.inr '' B₂` with `B₁, B₂` finite (`Set.Finite.image`, `Set.Finite.union`) — or `Filter.Tendsto.sum_elim`-type
   lemma if present. `map_add'`/`map_smul'`: `Prod.ext` + `ext; rfl`. Inverses: `ext x; cases x <;> rfl`. `norm_map'`: `Prod.norm_def`,
   then `le_antisymm` via `norm_le_of_forall_le`/`norm_apply_le` (a value at `inl i` is bounded by the first norm, …; `max_le`, `le_max_left`).
2. `prodEquiv`: inner tendsto `(tendsto_cofinite f).comp (Prod.mk.inj_left i).tendsto_cofinite`; outer tendsto is Layer 0's
   `Filter.Tendsto.iSup_norm_cofinite_left (tendsto_cofinite f)` after `norm_eq_iSup`; `invFun`'s tendsto is Layer 0's
   `tendsto_cofinite_prod_of_tendsto_iSup_norm` applied to `(tendsto_cofinite g).norm` rewritten with `norm_eq_iSup`.
   `map_add'`/`map_smul'`/inverses: `ext; rfl`. `norm_map'`: sandwich — `‖f (i, j)‖ ≤ ‖(prodEquiv f) i‖ ≤ ‖prodEquiv f‖` and
   `‖(prodEquiv f) i‖ ≤ ‖f‖` by `norm_le_of_forall_le`, hence equality by `le_antisymm`.

#### Mathlib lemmas needed
`Sum.inl_injective`, `Sum.inr_injective`, `Prod.mk.inj_left`, `Function.Injective.tendsto_cofinite`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.image`, `Set.Finite.union`, `Prod.norm_def`, `Filter.Tendsto.iSup_norm_cofinite_left` [L0], `tendsto_cofinite_prod_of_tendsto_iSup_norm` [L0], `norm_eq_iSup`.
#### Sources
[RM] §2.1.4 ("`C₀(I ⊕ J, R) ≃ₗᵢ C₀(I, R) × C₀(J, R)` with the max norm; `C₀(I × J, R) ≃ₗᵢ C₀(I, C₀(J, R))`").
#### Generality decision
Mathlib's product norm is the max norm (`Prod.norm_def`), as the roadmap requires.

### [T011] Finite index sets, the block decomposition, and functoriality in the values (isometric case)
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: T010 · **Parallel**: no · **Type**: definitions
- **Leaves**: L11.1–L11.3

#### Statement
```lean
noncomputable def piEquiv [Fintype I] : C₀(I, E) ≃ₗᵢ[R] (I → E) where
  toFun f := ⇑f
  invFun g := ofTendsto g (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

noncomputable def congrRight (e : E ≃ₗᵢ[R] F) : C₀(I, E) ≃ₗᵢ[R] C₀(I, F) where
  toFun f := ofTendsto (fun i ↦ e (f i)) (by sorry)
  invFun g := ofTendsto (fun i ↦ e.symm (g i)) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry
```
#### Proof sketch
1. `piEquiv`: `invFun`'s tendsto: on a finite type `cofinite = ⊥` (`Filter.cofinite_eq_bot`), so `tendsto_bot`. `map_add'`/`map_smul'`: `rfl`;
   `left_inv`: `ext; rfl`; `right_inv`: `rfl`. `norm_map'`: `le_antisymm (norm_le_of_forall_le (norm_nonneg _) fun i ↦ norm_le_pi_norm _ i)
   ((pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 (norm_apply_le f))`. `blockEquiv` and `setSumComplEquiv` are already terms.
2. `congrRight`: tendsto `((e.continuous.tendsto 0).comp (tendsto_cofinite f))` after `map_zero` (same for `e.symm`); `map_add'`/`map_smul'`:
   `ext; simp [map_add, map_smul]`; inverses: `ext; simp`; `norm_map'`: sandwich with `norm_le_of_forall_le`, `norm_apply_le` and `e.norm_map`.

#### Mathlib lemmas needed
`Filter.cofinite_eq_bot`, `tendsto_bot`, `norm_le_pi_norm`, `pi_norm_le_iff_of_nonneg`, `LinearIsometryEquiv.norm_map`, `LinearIsometryEquiv.continuous`, `map_zero`.
#### Sources
[RM] §2.1.4 ("for a finite `σ`, `C₀(σ × I, R) ≃ₗᵢ (σ → C₀(I, R))`, the block decomposition"); §2.2.3 (stability under `C₀(J, −)`).
#### Generality decision
`piEquiv` takes `[Fintype I]` because `Pi.normedAddCommGroup` does.

### [CLEANUP-4] Run `/cleanup` on `ModelSpace/Reindex.lean`
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: T009, T010, T011 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Reindex.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T012] Functoriality in the values over a Tate ring: `compL`, `congrRightL`
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: CLEANUP-4 · **Parallel**: no · **Type**: definitions
- **Leaves**: L12.1–L12.2

#### Statement
```lean
noncomputable def compL [NormOneClass R] [IsTate R] (u : E →L[R] F) :
    C₀(I, E) →L[R] C₀(I, F) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ u (f i)) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    ‖u‖ (by sorry)

noncomputable def congrRightL [NormOneClass R] [IsTate R] (e : E ≃L[R] F) :
    C₀(I, E) ≃L[R] C₀(I, F) :=
  ContinuousLinearEquiv.equivOfInverse (compL (e : E →L[R] F)) (compL (e.symm : F →L[R] E))
    (by sorry) (by sorry)
```
#### Proof sketch
1. `compL`: tendsto `((u.continuous.tendsto 0).comp (tendsto_cofinite f))` with `map_zero`; `map_add'`/`map_smul'`: `ext; simp`;
   the bound: `norm_le_of_forall_le (mul_nonneg (opNorm_nonneg u) (norm_nonneg f)) fun i ↦ (le_opNorm u (f i)).trans
   (mul_le_mul_of_nonneg_left (norm_apply_le f i) (opNorm_nonneg u))` (`[IsTate R]`).
2. `congrRightL`: the two inverse proofs `fun f ↦ by ext; simp [compL_apply, e.symm_apply_apply]` and `e.apply_symm_apply`.

#### Mathlib lemmas needed
`ContinuousLinearMap.Ultra.{le_opNorm, opNorm_nonneg}` [L1], `ContinuousLinearEquiv.{symm_apply_apply, apply_symm_apply}`, `ContinuousLinearEquiv.equivOfInverse`.
#### Sources
[RM] §2.2.3 (stability of potential orthonormalisability and (Pr) under `C₀(J, −)`); [L1] §1.1.2 (continuous = bounded over a Tate ring, which is why `[IsTate R]` is needed — seam S3).
#### Generality decision
`[NormOneClass R] [IsTate R]` written explicitly in the signatures (plan decision 10).

### [CLEANUP-5] Run `/cleanup` on `ModelSpace/Reindex.lean`
- **Status**: open · **File**: `ModelSpace/Reindex.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Reindex.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T013] Functoriality in the ring: `map φ`
- **Status**: open · **File**: `ModelSpace/Map.lean` · **Depends on**: CLEANUP-5 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L13.1–L13.5

#### Statement
```lean
noncomputable def map (φ : R →+* S) (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) :
    C₀(I, R) →SL[φ] C₀(I, S) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ φ (f i)) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    (max C 0) (by sorry)

theorem map_single [DecidableEq I] (φ : R →+* S) (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (i : I)
    (r : R) : map φ C hφ (single i r) = single i (φ r) := by
  sorry

theorem norm_map_apply_le (φ : R →+* S) {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (f : C₀(I, R)) : ‖map φ C hφ f‖ ≤ C * ‖f‖ := by
  sorry

theorem norm_map_apply_of_forall_norm_eq (φ : R →+* S) (hφ : ∀ r, ‖φ r‖ = ‖r‖) (f : C₀(I, R)) :
    ‖map φ 1 (fun r ↦ by rw [one_mul, hφ]) f‖ = ‖f‖ := by
  sorry

theorem map_reindex {J : Type*} [TopologicalSpace J] [DiscreteTopology J] (φ : R →+* S) (C : ℝ)
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (e : I ≃ J) (f : C₀(I, R)) :
    map φ C hφ (reindex (R := R) e f) = reindex (R := S) e (map φ C hφ f) := by
  sorry
```
#### Proof sketch
1. `map`'s tendsto: `squeeze_zero_norm (fun i ↦ (hφ (f i)).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)))`-style
   with the bound `max C 0 * ‖f i‖ → 0` (`(tendsto_cofinite f).norm.const_mul _`, `mul_zero`); `map_add'`: `ext; simp [map_add]`;
   `map_smul'`: `ext i; simp [smul_apply, smul_eq_mul, map_mul]` (`φ (r * f i) = φ r * φ (f i)` and the target action is `φ r • _`);
   the `mkContinuous` bound with `max C 0`: `norm_le_of_forall_le (mul_nonneg (le_max_right _ _) (norm_nonneg f)) fun i ↦
   (hφ (f i)).trans (mul_le_mul (le_max_left _ _) (norm_apply_le f i) (norm_nonneg _) (le_max_right _ _))`.
2. `map_single`: `ext j; by_cases h : j = i <;> simp [map_apply, coe_single, Pi.single_apply, h, map_zero]`.
3. `norm_map_apply_le`: `norm_le_of_forall_le (mul_nonneg hC (norm_nonneg f)) fun i ↦ (hφ (f i)).trans (mul_le_mul_of_nonneg_left (norm_apply_le f i) hC)`.
4. `norm_map_apply_of_forall_norm_eq`: `le_antisymm` via `norm_le_of_forall_le` twice, each coordinate by `hφ` and `norm_apply_le`.
5. `map_reindex`: `ext; rfl`.

#### Mathlib lemmas needed
`squeeze_zero_norm`, `Filter.Tendsto.const_mul`, `map_add`, `map_mul`, `map_zero`, `Pi.single_apply`, `mul_le_mul`, `le_max_left`, `le_max_right`.
#### Sources
[RM] §2.1.5 ("A bounded ring homomorphism `φ : R → S` induces `C₀(I, R) → C₀(I, S)` of norm at most the bound of `φ`, an isometry when `φ` is, and compatible with `single`, `eval`, and reindexing").
#### Generality decision
The bound `C` is an explicit argument; the `mkContinuous` constant is `max C 0` so the obligation holds for every `C` (plan decision 7); `norm_map_apply_le` takes `0 ≤ C`.

### [CLEANUP-6] Run `/cleanup` on `ModelSpace/Map.lean`
- **Status**: open · **File**: `ModelSpace/Map.lean` · **Depends on**: T013 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Map.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T014] Coordinate truncations: definition and pointwise lemmas
- **Status**: open · **File**: `ModelSpace/Truncation.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (parallel with T006–T013) · **Type**: definition + lemmas
- **Leaves**: L14.1–L14.8

#### Statement
```lean
noncomputable def truncation (S : Set I) [DecidablePred (· ∈ S)] : C₀(I, R) →L[R] C₀(I, R) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ if i ∈ S then f i else 0) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    1 (by sorry)

theorem truncation_apply_of_mem (f : C₀(I, R)) {i : I} (hi : i ∈ S) : truncation S f i = f i := by
  sorry

theorem truncation_apply_of_notMem (f : C₀(I, R)) {i : I} (hi : i ∉ S) :
    truncation S f i = 0 := by
  sorry

theorem norm_truncation_apply_le (f : C₀(I, R)) : ‖truncation S f‖ ≤ ‖f‖ := by
  sorry

theorem norm_truncation_le : ‖(truncation S : C₀(I, R) →L[R] C₀(I, R))‖ ≤ 1 := by
  sorry

theorem truncation_truncation (f : C₀(I, R)) : truncation S (truncation S f) = truncation S f := by
  sorry

theorem truncation_single [DecidableEq I] (i : I) (r : R) :
    truncation S (single i r) = if i ∈ S then single i r else 0 := by
  sorry

theorem norm_sub_truncation_le (f : C₀(I, R)) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i ∉ S, ‖f i‖ ≤ ε) :
    ‖f - truncation S f‖ ≤ ε := by
  sorry
```
#### Proof sketch
1. `truncation`'s tendsto: `squeeze_zero_norm (fun i ↦ by split_ifs <;> simp) (tendsto_cofinite f).norm` (`‖if i ∈ S then f i else 0‖ ≤ ‖f i‖`);
   `map_add'`/`map_smul'`: `ext i; simp only [...]; split_ifs <;> simp`; the bound `1`: `norm_le_of_forall_le (by simp) fun i ↦ by
   rw [one_mul]; split_ifs <;> simp [norm_apply_le]`.
2. `truncation_apply_of_mem`: `if_pos hi`; `truncation_apply_of_notMem`: `if_neg hi`.
3. `norm_truncation_apply_le`: `norm_le_of_forall_le (norm_nonneg f) fun i ↦ by rw [truncation_apply]; split_ifs <;> simp [norm_apply_le]`.
4. `norm_truncation_le`: `opNorm_le_bound _ zero_le_one fun f ↦ by rw [one_mul]; exact norm_truncation_apply_le S f`.
5. `truncation_truncation`: `ext i; simp only [truncation_apply]; split_ifs <;> rfl`.
6. `truncation_single`: `ext j; by_cases hj : j ∈ S <;> by_cases hji : j = i <;> simp [truncation_apply, coe_single, Pi.single_apply, *]`
   (the right-hand `if` is on `i ∈ S`; when `j = i` the two conditions agree).
7. `norm_sub_truncation_le`: `norm_le_of_forall_le hε fun i ↦ by rw [sub_apply, truncation_apply]; split_ifs with hi <;> simp [h i, *]`
   (`sub_self`, `norm_zero`, `sub_zero`, `h i hi`).

#### Mathlib lemmas needed
`squeeze_zero_norm`, `if_pos`, `if_neg`, `ContinuousLinearMap.Ultra.opNorm_le_bound` [L1], `Pi.single_apply`, `sub_apply`, `norm_apply_le`.
#### Sources
[RM] §2.6.3 ("the truncation `π_S : C₀(I, R) →L[R] C₀(I, R)` (restriction of coordinates to `S`) has norm at most `1`"); [Bel] l. 2038–2042 ("`π_S : M → M` the projection of `M` onto `M_S` sending `e_i` to `e_i` if `i ∈ S`, and `e_i` to `0` if `i ∉ S`").
#### Generality decision
Stated for an arbitrary `S : Set I` with `[DecidablePred (· ∈ S)]`; the finite case is `S = ↑s` for `s : Finset I`.

### [T015] The range of a truncation: closed direct summand, finite free module
- **Status**: open · **File**: `ModelSpace/Truncation.lean` · **Depends on**: T014 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L15.1–L15.3

#### Statement
```lean
theorem mem_range_truncation_iff {f : C₀(I, R)} :
    f ∈ LinearMap.range (truncation (R := R) S : C₀(I, R) →ₗ[R] C₀(I, R)) ↔ ∀ i ∉ S, f i = 0 := by
  sorry

theorem closedComplemented_range_truncation :
    (LinearMap.range (truncation (R := R) S : C₀(I, R) →ₗ[R] C₀(I, R))).ClosedComplemented := by
  sorry

theorem range_truncation_finset [DecidableEq I] (s : Finset I) :
    LinearMap.range (truncation (R := R) (↑s : Set I) : C₀(I, R) →ₗ[R] C₀(I, R)) =
      Submodule.span R (Set.range fun i : s ↦ single (i : I) (1 : R)) := by
  sorry
```
#### Proof sketch
1. `mem_range_truncation_iff`: `⟨by rintro ⟨g, rfl⟩ i hi; exact truncation_apply_of_notMem S g hi, fun h ↦ ⟨f, by ext i; rw [truncation_apply]; split_ifs with hi; · rfl; · exact (h i hi).symm⟩⟩`
   (`LinearMap.mem_range`).
2. `closedComplemented_range_truncation`: unfold `Submodule.ClosedComplemented` (`∃ f : E →L[R] p, ∀ x : p, f x = x`); take
   `(truncation S).codRestrict (LinearMap.range _) (fun g ↦ LinearMap.mem_range_self _ g)` and, for `x = ⟨_, g, rfl⟩`,
   `Subtype.ext (truncation_truncation S g)`.
3. `range_truncation_finset`: `le_antisymm`: (≤) `rintro _ ⟨g, rfl⟩`; `truncation ↑s g = ∑ i ∈ s, g i • single i 1` (`ext j`, `sum_apply`,
   `smul_single`, `coe_single`, `Finset.sum_pi_single'`), which is in the span (`Submodule.sum_mem`, `Submodule.smul_mem`,
   `Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩`); (≥) `Submodule.span_le.2`: `rintro _ ⟨⟨i, hi⟩, rfl⟩`; `mem_range_truncation_iff.2 fun j hj ↦
   single_apply_of_ne (fun h ↦ hj (h ▸ hi)) 1`.

#### Mathlib lemmas needed
`LinearMap.mem_range`, `LinearMap.mem_range_self`, `ContinuousLinearMap.codRestrict`, `Submodule.ClosedComplemented` (def), `Subtype.ext`, `Finset.sum_pi_single'`, `Submodule.span_le`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.
#### Sources
[RM] §2.6.3 ("has range the finite free module on `S`"), §2.2.5 ("the closed span of `e|_S` is a closed direct summand with the projection `π_S`"), the model-space case; [Bel] l. 2038–2042 ("`M_S` the finite free sub-module of `M` generated by the `e_s`, `s ∈ S`").
#### Generality decision
Any normed ring `R`.

### [T016] Truncations converge to the identity along finite subsets
- **Status**: open · **File**: `ModelSpace/Truncation.lean` · **Depends on**: T014 · **Parallel**: yes (parallel with T015) · **Type**: lemma
- **Leaves**: L16.1

#### Statement
```lean
theorem tendsto_truncation_finset [DecidableEq I] (f : C₀(I, R)) :
    Tendsto (fun s : Finset I ↦ truncation (↑s : Set I) f) atTop (𝓝 f) := by
  sorry
```
#### Proof sketch
`Metric.tendsto_atTop.2 fun ε hε ↦ ?_`. Let `B := {i | ¬ ‖f i‖ < ε / 2}`, finite by `Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1
(tendsto_cofinite f) (ε / 2) (half_pos hε))` (after `dist_zero_right`); take `N := B.toFinset`. For `s ≥ N`:
`dist (truncation ↑s f) f = ‖f - truncation ↑s f‖` (`dist_eq_norm'`), bounded by `ε / 2` through `norm_sub_truncation_le _ f (half_pos hε).le
fun i hi ↦ le_of_lt (not_not.1 fun h ↦ hi (hs (Set.Finite.mem_toFinset.2 h)))`, and `ε / 2 < ε`.

#### Mathlib lemmas needed
`Metric.tendsto_atTop`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.mem_toFinset`, `dist_eq_norm'`, `half_pos`, `half_lt_self`.
#### Sources
[RM] §2.6.3 ("`π_S ∘ u → u` pointwise along the filter of finite subsets for every bounded `u` into `C₀(I, R)`"); [Bel] proof of Prop II.1.9 l. 2062–2064 ("the sequence `(π_S ∘ φ)_{S ⊂ I, S finite}` converges").
#### Generality decision
Any normed ring; the `∘ u` form `tendsto_truncation_finset_comp` is already a term.

### [CLEANUP-7] Run `/cleanup` on `ModelSpace/Truncation.lean`
- **Status**: open · **File**: `ModelSpace/Truncation.lean` · **Depends on**: T015, T016 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Truncation.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T017] Orthogonal and `t`-orthogonal families: implications, independence, scaling, reindexing
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: T001, CLEANUP-3 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L17.2–L17.10

#### Statement
```lean
theorem IsOrthonormalFamily.isOrthogonalFamily (he : IsOrthonormalFamily R e) :
    IsOrthogonalFamily R e := by
  sorry

theorem IsOrthogonalFamily.isTOrthogonalFamily (he : IsOrthogonalFamily R e) {t : ℝ}
    (ht : t ≤ 1) : IsTOrthogonalFamily R t e := by
  sorry

theorem IsOrthogonalFamily.norm_smul_le_norm_sum (he : IsOrthogonalFamily R e) (s : Finset I)
    (a : I → R) {i : I} (hi : i ∈ s) : ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖ := by
  sorry

theorem IsOrthogonalFamily.linearIndependent [NormSMulClass R M] (he : IsOrthogonalFamily R e)
    (h0 : ∀ i, e i ≠ 0) : LinearIndependent R e := by
  sorry

theorem IsTOrthogonalFamily.linearIndependent [NormSMulClass R M] {t : ℝ} (ht : 0 < t)
    (he : IsTOrthogonalFamily R t e) (h0 : ∀ i, e i ≠ 0) : LinearIndependent R e := by
  sorry

theorem IsOrthogonalFamily.smul (he : IsOrthogonalFamily R e) (a : I → R) :
    IsOrthogonalFamily R fun i ↦ a i • e i := by
  sorry

theorem IsTOrthogonalFamily.smul {t : ℝ} (he : IsTOrthogonalFamily R t e) (a : I → R) :
    IsTOrthogonalFamily R t fun i ↦ a i • e i := by
  sorry

theorem IsOrthonormalFamily.comp_equiv {J : Type*} (he : IsOrthonormalFamily R e) (σ : J ≃ I) :
    IsOrthonormalFamily R (e ∘ σ) := by
  sorry

theorem IsOrthonormalBasis.comp_equiv {J : Type*} (he : IsOrthonormalBasis R e) (σ : J ≃ I) :
    IsOrthonormalBasis R (e ∘ σ) := by
  sorry
```
#### Proof sketch
1. `IsOrthonormalFamily.norm_smul_eq` (`‖a • eᵢ‖ = ‖a‖`) is proved in `Orthonormal.lean` (T001).
2. `isOrthogonalFamily`: `intro s a; rw [he.2 s a]; exact Finset.sup_congr rfl fun i _ ↦ by rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm, he.norm_smul_eq]`.
3. `isTOrthogonalFamily`: `intro s a i hi; exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (he.norm_smul_le_norm_sum s a hi)`.
4. `norm_smul_le_norm_sum`: `exact_mod_cast (he s a).symm ▸ Finset.le_sup (f := fun j ↦ ‖a j • e j‖₊) hi` (as in `Orthonormal.lean`'s `norm_coeff_le_norm_sum`).
5. `IsOrthogonalFamily.linearIndependent`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`; from `he.norm_smul_le_norm_sum s g hi` and
   `hg`, `‖g i • e i‖ ≤ 0`, so `g i • e i = 0` (`norm_le_zero_iff`); `norm_smul` gives `‖g i‖ * ‖e i‖ = 0`, and `norm_ne_zero_iff.2 (h0 i)`
   leaves `‖g i‖ = 0` (`mul_eq_zero`, `norm_eq_zero`).
6. `IsTOrthogonalFamily.linearIndependent`: the same with `t * ‖g i • e i‖ ≤ ‖0‖ = 0` and `ht` (`mul_nonneg`, `le_antisymm`).
7. `IsOrthogonalFamily.smul`: `intro s b; simp_rw [smul_smul]; exact he s fun i ↦ b i * a i`. 8. `IsTOrthogonalFamily.smul`: likewise.
9. `IsOrthonormalFamily.comp_equiv`: `⟨fun j ↦ he.1 (σ j), fun s a ↦ ?_⟩`; `have h := he.2 (s.map σ.toEmbedding) (a ∘ σ.symm)`; rewrite the sum with
   `Finset.sum_map` and the sup with `Finset.sup_map` (`σ.symm_apply_apply`), so that `h` is the goal.
10. `IsOrthonormalBasis.comp_equiv`: `⟨he.1.comp_equiv σ, by rwa [Set.range_comp, σ.surjective.range_eq? ]⟩` — concretely
   `Set.range (e ∘ σ) = Set.range e` by `σ.surjective.range_comp e` (`Function.Surjective.range_comp`).

#### Mathlib lemmas needed
`Finset.sum_singleton`, `Finset.sup_singleton`, `Finset.sup_congr`, `Finset.le_sup`, `NNReal.coe_inj`, `coe_nnnorm`, `mul_le_of_le_one_left`, `linearIndependent_iff'`, `norm_le_zero_iff`, `norm_smul`, `norm_ne_zero_iff`, `mul_eq_zero`, `smul_smul`, `Finset.sum_map`, `Finset.sup_map`, `Function.Surjective.range_comp`.
#### Sources
[RM] §2.2.1 ("orthonormal implies orthogonal implies `t`-orthogonal; an orthogonal family with nonzero members is linearly independent; the scaled family `aᵢ • eᵢ` of an orthogonal family is orthogonal"); [Sch] Prop 10.4 l. 3080–3083 ("We obviously can scale the vectors `vₙ` without changing the properties (a) and (b) and hence (c)"); E21 for the `NormSMulClass` hypothesis.
#### Generality decision
Any normed ring and normed module; `NormSMulClass R M` only for the two linear-independence lemmas about (`t`-)orthogonal families (E21).

### [T018] The isometric embedding of the model space given by an orthonormal family
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: T017, CLEANUP-3 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L18.1–L18.2

#### Statement
```lean
theorem IsOrthonormalFamily.norm_ofBounded_apply (he : IsOrthonormalFamily R e) (f : C₀(I, R)) :
    ‖ofBounded R e he.exists_bound f‖ = ‖f‖ := by
  sorry

theorem IsOrthonormalFamily.linearIsometry_single [DecidableEq I] (he : IsOrthonormalFamily R e)
    (i : I) : he.linearIsometry (single i 1) = e i := by
  sorry
```
#### Proof sketch
1. `norm_ofBounded_apply`: `le_antisymm`: (≤) `rw [ofBounded_apply]; exact IsUltrametricDist.norm_tsum_le_of_forall_le (norm_nonneg f)
   fun i ↦ by rw [he.norm_smul_eq]; exact norm_apply_le f i`; (≥) `rcases isEmpty_or_nonempty I` — if `I` is empty, `f = 0`
   (`eq_of_empty`) and both sides are `0`; otherwise `obtain ⟨i₀, hi₀⟩ := exists_norm_apply_eq_norm f` and
   `hi₀ ▸ he.norm_coeff_le_of_hasSum (hasSum_ofBounded R e he.exists_bound f) i₀` (the ring form from T001).
2. `linearIsometry_single`: `ofBounded_single R e he.exists_bound i`.

#### Mathlib lemmas needed
`IsUltrametricDist.norm_tsum_le_of_forall_le`, `isEmpty_or_nonempty`, `ZeroAtInftyContinuousMap.eq_of_empty`, `exists_norm_apply_eq_norm` (T002), `IsOrthonormalFamily.norm_coeff_le_of_hasSum` (T001), `hasSum_ofBounded`, `ofBounded_single` (T007–T008).
#### Sources
[RM] §2.2.1 ("for an orthonormal family the map `C₀(I, R) → M`, `a ↦ ∑' aᵢ • eᵢ` is an isometric embedding"); [Sch] Prop 10.1 l. 2975–2976 ("A continuity argument now shows that we have `‖f()‖ = ‖‖_∞` for any `` in `c₀(X)`").
#### Generality decision
`M` ultrametric and complete (for `ofBounded`), any normed ring `R`.

### [T019] Expansion coefficients of an orthonormal basis
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: T018 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L19.1–L19.6

#### Statement
```lean
theorem IsOrthonormalBasis.exists_hasSum' (he : IsOrthonormalBasis R e) (x : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) x := by
  sorry

theorem IsOrthonormalBasis.coeff_eq_of_hasSum (he : IsOrthonormalBasis R e) {a : I → R} {x : M}
    (ha : HasSum (fun i ↦ a i • e i) x) : he.coeff x = a := by
  sorry

theorem IsOrthonormalBasis.tendsto_coeff (he : IsOrthonormalBasis R e) (x : M) :
    Tendsto (he.coeff x) cofinite (𝓝 0) := by
  sorry

theorem IsOrthonormalBasis.norm_coeff_le (he : IsOrthonormalBasis R e) (x : M) (i : I) :
    ‖he.coeff x i‖ ≤ ‖x‖ := by
  sorry

theorem IsOrthonormalBasis.norm_eq_iSup_of_hasSum (he : IsOrthonormalBasis R e) {a : I → R} {x : M}
    (ha : HasSum (fun i ↦ a i • e i) x) : ‖x‖ = ⨆ i, ‖a i‖ := by
  sorry

noncomputable def IsOrthonormalBasis.coeffCLM (he : IsOrthonormalBasis R e) (i : I) : M →L[R] R :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ he.coeff x i
      map_add' := by sorry
      map_smul' := by sorry }
    1 (fun x ↦ by rw [one_mul]; exact he.norm_coeff_le x i)
```
#### Proof sketch
1. `exists_hasSum'`: `he.exists_hasSum x` (T001's ring form; if T001 kept a field-only `exists_hasSum`, prove it here by the same Cauchy argument).
2. `coeff_eq_of_hasSum`: `he.1.eq_of_hasSum (he.hasSum_coeff x) ha` (check the argument order of `eq_of_hasSum`).
3. `tendsto_coeff`: `he.1.tendsto_cofinite_of_hasSum (he.hasSum_coeff x)`. 4. `norm_coeff_le`: `he.1.norm_coeff_le_of_hasSum (he.hasSum_coeff x) i`.
5. `norm_eq_iSup_of_hasSum`: `le_antisymm (he.1.norm_le_of_hasSum ha (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun i ↦ le_ciSup ⟨‖x‖, by rintro _ ⟨i, rfl⟩; exact he.1.norm_coeff_le_of_hasSum ha i⟩ i)
   (Real.iSup_le (fun i ↦ he.1.norm_coeff_le_of_hasSum ha i) (norm_nonneg x))`.
6. `coeffCLM`'s `map_add'`: `he.coeff_eq_of_hasSum (by simpa only [add_smul] using (he.hasSum_coeff x).add (he.hasSum_coeff y)) ▸ rfl`-style
   (show `he.coeff (x + y) = he.coeff x + he.coeff y` then `congrFun`); `map_smul'`: `(he.hasSum_coeff x).const_smul r` with `smul_smul`.

#### Mathlib lemmas needed
`IsOrthonormalFamily.{eq_of_hasSum, tendsto_cofinite_of_hasSum, norm_coeff_le_of_hasSum, norm_le_of_hasSum}` (T001), `Real.iSup_le`, `le_ciSup`, `Real.iSup_nonneg`, `HasSum.add`, `HasSum.const_smul`, `add_smul`, `smul_smul`.
#### Sources
[RM] §2.2.2 ("every `x` has a unique expansion `x = ∑' aᵢ • eᵢ` with `a → 0` cofinitely, and then `‖x‖ = sup ‖aᵢ‖` … and the expansion coefficients are continuous linear functionals"); [Bel] Def II.1.5 l. 2010–2015.
#### Generality decision
`[CompleteSpace R]` for the existence of expansions (Layer 0's `exists_hasSum` docstring explains why); the coefficient functional has norm at most `1` by `norm_coeff_le`.

### [CLEANUP-8] Run `/cleanup` on `Orthogonal.lean`
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: T017, T018, T019 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Orthogonal.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T020] The Bellaïche–Colmez characterisation of orthonormal bases
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: CLEANUP-8 · **Parallel**: no · **Type**: lemma
- **Leaves**: L20.1

#### Statement
```lean
theorem isOrthonormalBasis_of_forall_hasSum [NormOneClass R]
    (h₁ : ∀ x : M, ∃ a : I → R, HasSum (fun i ↦ a i • e i) x)
    (h₂ : ∀ (a : I → R) (x : M), HasSum (fun i ↦ a i • e i) x → ‖x‖ = ⨆ i, ‖a i‖) :
    IsOrthonormalBasis R e := by
  sorry
```
#### Proof sketch
`refine ⟨⟨fun i ↦ ?_, fun s a ↦ ?_⟩, ?_⟩`.
1. `‖e i‖ = 1`: apply `h₂ (Pi.single i 1) (e i)` to `HasSum (fun j ↦ Pi.single i (1 : R) j • e j) (e i)`, which is `hasSum_single i`
   after `Pi.single_eq_of_ne`/`zero_smul` off `i` and `Pi.single_eq_same`/`one_smul` at `i`; the right-hand side `⨆ j, ‖Pi.single i 1 j‖` is `1`:
   `le_antisymm (Real.iSup_le (fun j ↦ by by_cases h : j = i <;> simp [h, norm_one]) zero_le_one) (le_ciSup_of_le ⟨1, …⟩ i (by simp [norm_one]))`.
2. The identity: apply `h₂ (fun j ↦ if j ∈ s then a j else 0) (∑ j ∈ s, a j • e j)` to `hasSum_sum_of_ne_finset_zero (fun j hj ↦ by simp [hj])`
   (after `Finset.sum_congr` with `if_pos`); then convert `⨆ j, ‖if j ∈ s then a j else 0‖` to `↑(s.sup fun j ↦ ‖a j‖₊)`: both `≤` by
   `Real.iSup_le`/`Finset.sup_le` and `Finset.le_sup`/`le_ciSup_of_le` (`coe_nnnorm`, `NNReal.coe_le_coe`); finish with `NNReal.coe_inj`.
3. Density: `Metric.dense_iff`/`mem_closure_iff_seq_limit` is not needed: for `x`, `obtain ⟨a, ha⟩ := h₁ x`; `ha` is
   `Tendsto (fun s ↦ ∑ i ∈ s, a i • e i) atTop (𝓝 x)`, and each partial sum lies in the span (`Submodule.sum_mem`, `Submodule.smul_mem`,
   `Submodule.subset_span ⟨i, rfl⟩`), so `mem_closure_of_tendsto ha (Filter.Eventually.of_forall …)`; `Dense` is `∀ x, x ∈ closure _`.

#### Mathlib lemmas needed
`hasSum_single`, `hasSum_sum_of_ne_finset_zero`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `Real.iSup_le`, `le_ciSup_of_le`, `Finset.sup_le`, `Finset.le_sup`, `coe_nnnorm`, `NNReal.coe_le_coe`, `NNReal.coe_inj`, `mem_closure_of_tendsto`, `Filter.Eventually.of_forall`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.
#### Sources
[RM] §2.2.2 ("Prove the equivalent formulations … (Bellaïche's Definition II.1.5, Colmez's Définition 1.1.3)"); [Bel] Def II.1.5 l. 2010–2015; [Col] Déf 1.1.3 l. 95–112 ("(i) tout élément `x` de `B` peut s'écrire de manière unique … (ii) `v_B(x) = inf_i v_p(a_i)`").
#### Generality decision
`[NormOneClass R]` for `‖e i‖ = ‖1‖ = 1`; the uniqueness of expansions is a consequence of the norm formula, so it is not assumed (plan design).

### [CLEANUP-9] Run `/cleanup` on `Orthogonal.lean`
- **Status**: open · **File**: `Orthogonal.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Orthogonal.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T021] ON-ability: the implications, the model space and its canonical basis
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T020, CLEANUP-5, CLEANUP-7 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L21.1–L21.6

#### Statement
```lean
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M := by
  sorry

theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R M) : HasPr R M := by
  sorry

theorem isONable_zeroAtInfty (R : Type u) [NormedRing R] (I : Type w) [TopologicalSpace I]
    [DiscreteTopology I] : IsONable R C₀(I, R) := by
  sorry

theorem isOrthonormalBasis_single [NormOneClass R] [DecidableEq I] :
    IsOrthonormalBasis R fun i : I ↦ single i (1 : R) := by
  sorry

theorem LinearIsometryEquiv.isOrthonormalBasis_symm_single [NormOneClass R] [DecidableEq I]
    (e : M ≃ₗᵢ[R] C₀(I, R)) : IsOrthonormalBasis R fun i ↦ e.symm (single i 1) := by
  sorry

theorem IsOrthonormalFamily.injective [NormOneClass R] {e : I → M} (he : IsOrthonormalFamily R e) :
    Injective e := by
  sorry
```
#### Proof sketch
1. `IsONable.isPotentiallyONable`: `obtain ⟨I, _, _, ⟨e⟩⟩ := h; exact ⟨I, _, _, ⟨e.toContinuousLinearEquiv⟩⟩`.
2. `IsPotentiallyONable.hasPr`: `obtain ⟨I, _, _, ⟨e⟩⟩ := h; exact ⟨I, _, _, e, e.symm, e.symm_comp_self⟩` (`ContinuousLinearEquiv.symm_comp_self`).
3. `isONable_zeroAtInfty`: `⟨ULift.{u} I, inferInstance, inferInstance, ⟨reindex (R := R) (E := R) Equiv.ulift.symm⟩⟩`.
4. `isOrthonormalBasis_single`: `⟨⟨fun i ↦ by rw [norm_single, norm_one], fun s a ↦ ?_⟩, dense_span_range_single_one⟩`; pointwise
   `(∑ i ∈ s, a i • single i 1) j = if j ∈ s then a j else 0` (`sum_apply`, `smul_single`, `smul_eq_mul`, `mul_one`, `Finset.sum_pi_single'`),
   then the nnnorm identity by `le_antisymm`: `‖∑‖₊ ≤ sup` from `norm_le_of_forall_le` (every coordinate is some `‖a j‖` or `0`, bounded by
   the sup via `Finset.le_sup`), and `‖a j‖₊ ≤ ‖∑‖₊` for `j ∈ s` from `norm_apply_le` at `j` (`NNReal.coe_le_coe`, `coe_nnnorm`).
5. `LinearIsometryEquiv.isOrthonormalBasis_symm_single`: `⟨⟨fun i ↦ by rw [e.symm.norm_map, norm_single, norm_one], fun s a ↦ ?_⟩, ?_⟩`;
   `∑ a i • e.symm (single i 1) = e.symm (∑ a i • single i 1)` (`map_sum`, `map_smul`), `e.symm.nnnorm_map`, then `isOrthonormalBasis_single.1.2`;
   density: `Submodule.span R (Set.range fun i ↦ e.symm (single i 1)) = (Submodule.span R (Set.range fun i ↦ single i 1)).map e.symm.toLinearEquiv`
   (`Submodule.map_span`, `Set.range_comp`) and `DenseRange.dense_image e.symm.surjective.denseRange e.symm.continuous dense_span_range_single_one`.
6. `IsOrthonormalFamily.injective`: `fun i j hij ↦ by_contra fun h ↦ ?_`; with `a k := if k = i then (1 : R) else -1` on `s := {i, j}`:
   `∑ k ∈ {i, j}, a k • e k = e i - e j = 0` (`Finset.sum_pair h`, `one_smul`, `neg_smul`, `hij`, `sub_self`), so by `he.2` the sup
   `{i, j}.sup ‖a k‖₊ = 1` (`Finset.sup_insert`, `Finset.sup_singleton`, `nnnorm_one`, `nnnorm_neg`) equals `‖0‖₊ = 0`, contradicting `one_ne_zero`.

#### Mathlib lemmas needed
`LinearIsometryEquiv.toContinuousLinearEquiv`, `ContinuousLinearEquiv.symm_comp_self`, `Equiv.ulift`, `Finset.sum_pi_single'`, `LinearIsometryEquiv.{norm_map, nnnorm_map, surjective, continuous}`, `map_sum`, `map_smul`, `Submodule.map_span`, `Set.range_comp`, `DenseRange.dense_image`, `Function.Surjective.denseRange`, `Finset.sum_pair`, `Finset.sup_insert`, `Finset.sup_singleton`, `nnnorm_one`, `nnnorm_neg`.
#### Sources
[RM] §2.2.3 ("an isometry `M ≃ₗᵢ C₀(I, R)` corresponds to the basis `i ↦ e⁻¹ (single i 1)` … prove that `C₀(I, R)` is ON-able with the canonical basis"); [Bel] Ex II.1.7 l. 2017–2021; [Buz07] l. 243–248 ("to give an ON basis for `M` is to give an isometric isomorphism `M ≅ c_A(I)`"); [JN] Def 2.1.5 l. 537–541.
#### Generality decision
`[NormOneClass R]` wherever `‖single i 1‖ = 1` is used; the index universe is handled by `ULift` (plan decision 3).

### [T022] Stability of the three notions under transport, finite products and `C₀(J, −)`
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T021, CLEANUP-5 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L22.1–L22.9

#### Statement
```lean
theorem IsONable.of_linearIsometryEquiv (e : M ≃ₗᵢ[R] N) (h : IsONable R M) : IsONable R N := by
  sorry

theorem IsPotentiallyONable.of_continuousLinearEquiv (e : M ≃L[R] N)
    (h : IsPotentiallyONable R M) : IsPotentiallyONable R N := by
  sorry

theorem HasPr.of_continuousLinearEquiv (e : M ≃L[R] N) (h : HasPr R M) : HasPr R N := by
  sorry

theorem IsONable.prod (hM : IsONable R M) (hN : IsONable R N) : IsONable R (M × N) := by
  sorry

theorem IsPotentiallyONable.prod (hM : IsPotentiallyONable R M) (hN : IsPotentiallyONable R N) :
    IsPotentiallyONable R (M × N) := by
  sorry

theorem HasPr.prod (hM : HasPr R M) (hN : HasPr R N) : HasPr R (M × N) := by
  sorry

theorem IsONable.zeroAtInfty (h : IsONable R M) : IsONable R C₀(J, M) := by
  sorry

theorem IsPotentiallyONable.zeroAtInfty [NormOneClass R] [IsTate R] (h : IsPotentiallyONable R M) :
    IsPotentiallyONable R C₀(J, M) := by
  sorry

theorem HasPr.zeroAtInfty [NormOneClass R] [IsTate R] (h : HasPr R M) : HasPr R C₀(J, M) := by
  sorry
```
#### Proof sketch
1. `of_linearIsometryEquiv`: `obtain ⟨I, _, _, ⟨f⟩⟩ := h; exact ⟨I, _, _, ⟨e.symm.trans f⟩⟩`; `of_continuousLinearEquiv` (potential): the same with `ContinuousLinearEquiv.trans`;
   `HasPr.of_continuousLinearEquiv`: `⟨I, _, _, ι.comp e.symm, e.toContinuousLinearMap.comp π, by ext; simp [h']⟩` where `h' : π.comp ι = id` is used through `congrArg`.
2. `IsONable.prod`: a private `prodCongr (e : M ≃ₗᵢ[R] M') (f : N ≃ₗᵢ[R] N') : M × N ≃ₗᵢ[R] M' × N'` built from `e.toLinearEquiv.prodCongr f.toLinearEquiv`
   with `norm_map'` by `Prod.norm_def` and the two `norm_map`; then `⟨I ⊕ J, _, _, ⟨(prodCongr e f).trans sumEquiv.symm⟩⟩`.
   `IsPotentiallyONable.prod`: `(ContinuousLinearEquiv.prodCongr e f).trans sumEquiv.symm.toContinuousLinearEquiv`.
   `HasPr.prod`: `ι := sumEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (ι₁.prodMap ι₂)`, `π := (π₁.prodMap π₂).comp sumEquiv.toContinuousLinearEquiv.toContinuousLinearMap`;
   `π.comp ι = id` by `ext ⟨x, y⟩ <;> simp [h₁', h₂']`.
3. `IsONable.zeroAtInfty`: `⟨J × I, _, _, ⟨(congrRight e).trans prodEquiv.symm⟩⟩` (index `J × I : Type v`).
   `IsPotentiallyONable.zeroAtInfty`: `(congrRightL e).trans prodEquiv.symm.toContinuousLinearEquiv`.
   `HasPr.zeroAtInfty`: `ι' := prodEquiv.symm… ∘ compL ι`, `π' := compL π ∘ prodEquiv…`; `compL π ∘ compL ι = compL (π ∘ ι) = compL id = id` by `ext; simp [compL_apply, h']`.

#### Mathlib lemmas needed
`LinearIsometryEquiv.trans`, `ContinuousLinearEquiv.trans`, `LinearEquiv.prodCongr`, `Prod.norm_def`, `ContinuousLinearEquiv.prodCongr`, `ContinuousLinearMap.prodMap`, `sumEquiv`, `prodEquiv`, `congrRight`, `congrRightL`, `compL` (T010–T012).
#### Sources
[RM] §2.2.3 ("all three notions are stable under reindexing, finite products, `C₀(J, −)`, and bounded-equivalent norms (potentially ON-able and (Pr) only)"); [JN] l. 657–659 ("having property (Pr) is stable when changing the norms on `(R, M)` to equivalent ones").
#### Generality decision
Targets stay in universe `v` (plan decision 3); the `C₀(J, −)` statements for the potential notions need `[IsTate R]` (seam S3).

### [CLEANUP-ALL-1] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: T022, CLEANUP-9 · **Parallel**: no · **Type**: cleanup
- **Description**: Pre-milestone sweep before M1 (`/cleanup-all` on the board's files). Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T023] MILESTONE M1 — orthonormalisable means having an orthonormal basis
- **Status**: open · **File**: `ONable.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: milestone
- **Leaves**: L23.1–L23.3

#### Statement
```lean
theorem IsOrthonormalBasis.surjective_linearIsometry (he : IsOrthonormalBasis R e) :
    Surjective he.1.linearIsometry := by
  sorry

theorem IsOrthonormalBasis.isONable [NormOneClass R] (he : IsOrthonormalBasis R e) :
    IsONable R M := by
  sorry

theorem Module.isONable_iff_exists_isOrthonormalBasis [NormOneClass R] :
    IsONable R M ↔ ∃ (I : Type v) (e : I → M), IsOrthonormalBasis R e := by
  sorry
```
#### Proof sketch
1. `surjective_linearIsometry`: `intro x; obtain ⟨a, ha⟩ := he.exists_hasSum' x`; `refine ⟨ofTendsto a (he.1.tendsto_cofinite_of_hasSum ha), ?_⟩`;
   `rw [linearIsometry_apply]; exact ha.tsum_eq` (`coe_ofTendsto`).
2. `IsOrthonormalBasis.isONable`: `letI : TopologicalSpace (Set.range e) := ⊥; haveI : DiscreteTopology (Set.range e) := discreteTopology_bot _`
   (**the subtype would otherwise inherit the topology of `M`**); `σ := (Equiv.ofInjective e he.1.injective).symm : Set.range e ≃ I`;
   `exact ⟨Set.range e, ⊥, inferInstance, ⟨(he.comp_equiv σ).linearIsometryEquiv.symm⟩⟩`.
3. `isONable_iff_exists_isOrthonormalBasis`: `⟨fun ⟨I, _, _, ⟨Φ⟩⟩ ↦ by classical exact ⟨I, _, Φ.isOrthonormalBasis_symm_single⟩, fun ⟨I, e, he⟩ ↦ he.isONable⟩`.

#### Mathlib lemmas needed
`Filter.Tendsto` (T019's `tendsto_coeff` form), `HasSum.tsum_eq`, `discreteTopology_bot`, `Equiv.ofInjective`, `LinearIsometryEquiv.ofSurjective`, `IsOrthonormalBasis.comp_equiv` (T017), `LinearIsometryEquiv.isOrthonormalBasis_symm_single` (T021).
#### Sources
[RM] §2.2.3 ("`IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`"); [Buz07] l. 246–248; [Bel] Ex II.1.7 l. 2021–2024 ("A Banach `R`-module `M` is orthonormalizable … if and only if it is isometric … to `c_I(R)` for some set `I`"); [Sch] Prop 10.1 l. 2977–2981 (surjectivity via density).
#### Generality decision
`[CompleteSpace R]` (expansions), `M` ultrametric complete, `[NormOneClass R]`; the index set of the basis lives in any universe, the theorem's in `v` (decision 3).

### [CLEANUP-10] Run `/cleanup` on `ONable.lean`
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T021, T022, T023 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `ONable.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T024] Direct summands and (Pr)
- **Status**: open · **File**: `ONable.lean` · **Depends on**: CLEANUP-10 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L24.1–L24.2

#### Statement
```lean
theorem Submodule.ClosedComplemented.hasPr (hM : IsPotentiallyONable R M) {p : Submodule R M}
    (hp : p.ClosedComplemented) : HasPr R p := by
  sorry

theorem Module.HasPr.exists_closedComplemented (h : HasPr R M) :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (p : Submodule R C₀(I, R)),
      p.ClosedComplemented ∧ Nonempty (M ≃L[R] p) := by
  sorry
```
#### Proof sketch
1. `Submodule.ClosedComplemented.hasPr`: `obtain ⟨I, _, _, ⟨e⟩⟩ := hM; obtain ⟨f, hf⟩ := hp` (`f : M →L[R] p`, `∀ x : p, f x = x`);
   `exact ⟨I, _, _, e.toContinuousLinearMap.comp p.subtypeL, f.comp e.symm.toContinuousLinearMap, by ext x; simp [hf]⟩`.
2. `HasPr.exists_closedComplemented`: `obtain ⟨I, _, _, ι, π, h⟩ := h`; `p := LinearMap.range (ι : M →ₗ[R] C₀(I, R))`; the projector
   `(ι.comp π).codRestrict p (fun x ↦ LinearMap.mem_range_self _ _)` fixes `p` pointwise (`rintro ⟨_, m, rfl⟩; exact Subtype.ext (by simp [congrArg (· m) h])`);
   `M ≃L[R] p` by `ContinuousLinearEquiv.equivOfInverse (ι.codRestrict p _) (π.comp p.subtypeL) (fun m ↦ by simp [congrArg (· m) h]) (by rintro ⟨_, m, rfl⟩; exact Subtype.ext (by simp [congrArg (· m) h]))`.

#### Mathlib lemmas needed
`Submodule.subtypeL`, `ContinuousLinearMap.codRestrict`, `LinearMap.mem_range_self`, `ContinuousLinearEquiv.equivOfInverse`, `Subtype.ext`.
#### Sources
[RM] §2.2.3 ("a closed direct summand of a potentially ON-able module has (Pr)"), convention 4; [Bel] II.1.6 l. 2223–2225 ("`P` has property (Pr) if there exists a Banach module `Q` such that `P ⊕ Q` is potentially orthonormalizable"); [JN] l. 543–545.
#### Generality decision
The retract form of `HasPr` (decision 4) makes both directions one-liners; no completeness needed.

### [T025] Orthogonal complements and projections for an orthonormal basis (§2.2.5)
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T024 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L25.1–L25.3

#### Statement
```lean
theorem IsOrthonormalBasis.closedComplemented_topologicalClosure_span (he : IsOrthonormalBasis R e)
    (S : Set I) : (Submodule.span R (e '' S)).topologicalClosure.ClosedComplemented := by
  sorry

theorem IsOrthonormalBasis.exists_projection (he : IsOrthonormalBasis R e) (S : Set I) :
    ∃ π : M →L[R] M, (∀ x, ‖π x‖ ≤ ‖x‖) ∧
      (∀ x, π x ∈ (Submodule.span R (e '' S)).topologicalClosure) ∧
      ∀ x ∈ (Submodule.span R (e '' S)).topologicalClosure, π x = x := by
  sorry

theorem IsOrthonormalBasis.nonempty_linearIsometryEquiv_prod (he : IsOrthonormalBasis R e)
    (S : Set I) [DecidablePred (· ∈ S)] :
    Nonempty (M ≃ₗᵢ[R] C₀(S, R) × C₀((Sᶜ : Set I), R)) := by
  sorry
```
#### Proof sketch
Let `Φ := he.linearIsometryEquiv : C₀(I, R) ≃ₗᵢ[R] M` and `T := truncation S` (classical `DecidablePred`).
0. Key identity: `(Submodule.span R (e '' S)).topologicalClosure = (LinearMap.range (T : C₀(I, R) →ₗ[R] C₀(I, R))).map Φ.toLinearEquiv`.
   (⊇) for `g`, `Φ (T g) = ∑' i, (T g) i • e i` is the limit of partial sums `∑ i ∈ s, (T g) i • e i ∈ span (e '' S)` (only `i ∈ S` contribute),
   so `mem_closure_of_tendsto` (`Submodule.topologicalClosure_coe`); (⊆) `Submodule.topologicalClosure_minimal`: `span (e '' S) ≤ map Φ (range T)`
   since `e i = Φ (single i 1) = Φ (T (single i 1))` for `i ∈ S` (`truncation_single`, `linearIsometryEquiv_single`), and `map Φ (range T)` is closed:
   `range T = ker (id - T)` (`truncation_truncation`) is closed (`ContinuousLinearMap.isClosed_ker`) and `Φ.toHomeomorph.isClosed_image`.
1. `closedComplemented_topologicalClosure_span`: rewrite with the key identity; the projector is `Φ ∘ T ∘ Φ.symm` cod-restricted
   (`ContinuousLinearMap.codRestrict`), fixing the range pointwise by `truncation_truncation`.
2. `exists_projection`: `π := Φ.toContinuousLinearEquiv.toContinuousLinearMap.comp (T.comp Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap)`;
   `‖π x‖ = ‖T (Φ.symm x)‖ ≤ ‖Φ.symm x‖ = ‖x‖` (`norm_truncation_apply_le`, `norm_map`); membership and the fixed points from the key identity.
3. `nonempty_linearIsometryEquiv_prod`: `⟨Φ.symm.trans (setSumComplEquiv S)⟩`.

#### Mathlib lemmas needed
`Submodule.topologicalClosure_coe`, `Submodule.topologicalClosure_minimal`, `Submodule.map_span`, `mem_closure_of_tendsto`, `ContinuousLinearMap.isClosed_ker`, `Homeomorph.isClosed_image`, `ContinuousLinearMap.codRestrict`, `truncation_single`, `truncation_truncation`, `norm_truncation_apply_le` (T014), `setSumComplEquiv` (T011).
#### Sources
[RM] §2.2.5 ("For an orthonormal basis `e` and a subset `S ⊆ I`, the closed span of `e|_S` is a closed direct summand with the projection `π_S` of norm at most `1`, and `M ≅ C₀(S, R) × C₀(I ∖ S, R)`"); [Bel] l. 2038–2042 (`M_S`, `π_S`).
#### Generality decision
Everything is transported from the model-space statements of T015 along `Φ`; `[CompleteSpace R]` and `M` Banach because `Φ` needs them.

### [T026] The lifting property of (Pr)
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T024, CLEANUP-5 · **Parallel**: yes (parallel with T025) · **Type**: lemmas
- **Leaves**: L26.1–L26.4

#### Statement
```lean
theorem ZeroAtInftyContinuousMap.exists_lift {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    (u : N →L[R] N') (hu : Surjective u) (v : C₀(I, R) →L[R] N') :
    ∃ w : C₀(I, R) →L[R] N, u.comp w = v := by
  sorry

theorem Module.HasPr.exists_lift (hM : HasPr R M) (u : N →L[R] N') (hu : Surjective u)
    (v : M →L[R] N') : ∃ w : M →L[R] N, u.comp w = v := by
  sorry

theorem Module.exists_surjective_zeroAtInfty [IsUltrametricDist M] [CompleteSpace M] :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (u : C₀(I, R) →L[R] M),
      Surjective u := by
  sorry

theorem Module.hasPr_of_forall_exists_lift [IsUltrametricDist M] [CompleteSpace M]
    (h : ∀ (N : Type (max u v)) (N' : Type v) [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
      [IsUltrametricDist N] [CompleteSpace N] [NormedAddCommGroup N'] [Module R N']
      [IsBoundedSMul R N'] [CompleteSpace N'] (u : N →L[R] N'), Surjective u →
      ∀ v : M →L[R] N', ∃ w : M →L[R] N, u.comp w = v) : HasPr R M := by
  sorry
```
#### Proof sketch
1. `ZeroAtInftyContinuousMap.exists_lift`: `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le u hu` (Layer 1 OMT, needs `N`, `N'` complete);
   `choose g hg using hC`; `obtain ⟨D, hD⟩ := exists_bound_single v`; `m i := g (v (single i 1))` is bounded by `C * D`
   (`(hg _).2`, `mul_le_mul_of_nonneg_left`); `w := ofBounded R m ⟨C * D, _⟩`; `u.comp w = v` by `ext_single fun i ↦ by rw [comp_apply, ofBounded_single, (hg _).1]`.
2. `HasPr.exists_lift`: `obtain ⟨I, _, _, ι, π, hπι⟩ := hM`; `obtain ⟨w₀, hw₀⟩ := ZeroAtInftyContinuousMap.exists_lift u hu (v.comp π)`;
   `⟨w₀.comp ι, by rw [← comp_assoc, hw₀, comp_assoc, hπι, comp_id]⟩`.
3. `exists_surjective_zeroAtInfty`: `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)`; index `I := {x : M // ‖x‖ ≤ 1}` with
   `letI : TopologicalSpace I := ⊥` and `discreteTopology_bot`; `u := ofBounded R (fun x : I ↦ (x : M)) ⟨1, fun x ↦ x.2⟩`; for `y`:
   if `y = 0` use `0`; else `obtain ⟨n, ⟨-, hn⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc_one hy` (`‖(ϖ.unit ^ n : R) • y‖ ≤ 1`),
   `x : I := ⟨(ϖ.unit ^ n : R) • y, hn⟩`, `f := single x ((ϖ.unit ^ (-n) : Rˣ) : R)`; `u f = ((ϖ.unit ^ (-n)) : R) • x` (`smul_single`, `ofBounded_single`, `map_smul`)
   `= y` (`smul_smul`, `← Units.val_mul`, `zpow_neg_add? ` i.e. `ϖ.unit ^ (-n) * ϖ.unit ^ n = 1`, `one_smul`).
4. `hasPr_of_forall_exists_lift`: `obtain ⟨I, _, _, u, hu⟩ := exists_surjective_zeroAtInfty (R := R) (M := M)`;
   `obtain ⟨w, hw⟩ := h C₀(I, R) M u hu (ContinuousLinearMap.id R M)`; `exact ⟨I, _, _, w, u, hw⟩`.

#### Mathlib lemmas needed
`ContinuousLinearMap.Ultra.exists_preimage_norm_le` [L1], `exists_bound_single` (T006), `ofBounded_single`, `ext_single`, `ContinuousLinearMap.{comp_assoc, comp_id, id_comp}`, `NormedRing.IsTate.exists_pseudoUniformizer`, `NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc_one` [L0], `zpow_neg`, `Units.val_mul`, `discreteTopology_bot`.
#### Sources
[RM] §2.2.4 ("A Banach module `P` has property (Pr) if and only if every continuous surjection `M → N` of Banach modules and every continuous map `P → N` admit a continuous lift `P → M` (Bellaïche, Exercise II.1.19)"); [Bel] Ex II.1.19 l. 2226–2228; [Sch] Prop 10.5 l. 3128–3137 (the lift of the `1_x` with the bound `c⁻¹` and the universal property).
#### Generality decision
The surjection from a model space uses the unit ball of `M` as index (universe `v`) and the scaling trick (needs `[IsTate R]`); `N : Type (max u v)`, `N' : Type v` in the characterisation (E29).

### [CLEANUP-11] Run `/cleanup` on `ONable.lean`
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T024, T025, T026 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `ONable.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T027] A finitely generated module with (Pr) is projective (Bellaïche II.1.20)
- **Status**: open · **File**: `ONable.lean` · **Depends on**: CLEANUP-11 · **Parallel**: no · **Type**: lemma
- **Leaves**: L27.1

#### Statement
```lean
theorem Module.HasPr.projective [CompleteSpace R] [IsUltrametricDist R] [IsUltrametricDist M]
    [CompleteSpace M] [Module.Finite R M] (hM : HasPr R M) : Module.Projective R M := by
  sorry
```
#### Proof sketch
`obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M` (a surjective `f : (Fin n → R) →ₗ[R] M`); `fL : (Fin n → R) →L[R] M := ⟨f, continuous_pi f⟩`
(Layer 1 `Pi.lean`); `Fin n → R` is a Banach ultrametric module (`[CompleteSpace R]`, `[IsUltrametricDist R]`, the `Pi` instances);
`obtain ⟨w, hw⟩ := hM.exists_lift fL hf (ContinuousLinearMap.id R M)`; conclude with
`Module.Projective.of_split (w : M →ₗ[R] (Fin n → R)) f (by ext m; exact congrArg (· m) hw)` (`Module.Projective (Fin n → R)` from `Module.Free`).

#### Mathlib lemmas needed
`Module.Finite.exists_fin'`, `ContinuousLinearMap.Ultra.continuous_pi` [L1], `Module.Projective.of_split`, `Module.Free.projective` (instance), the `Pi` ultrametric instance (`Mathlib.Topology.MetricSpace.Ultra.Pi`).
#### Sources
[RM] §2.2.4 ("a finitely generated module with (Pr) is projective (Bellaïche, Proposition II.1.20)"); [Bel] Prop II.1.20 l. 2229–2235 ("choose a surjective continuous map `f : A^r → P` and apply Exercise II.1.19 to `α = Id_P`… `P ≃ β(P)` is a direct summand of `A^r`").
#### Generality decision
Needs `M` Banach (the lift uses the OMT on `fL`), `R` Banach–Tate and ultrametric (for `Fin n → R` to be an admissible `N`).

### [CLEANUP-12] Run `/cleanup` on `ONable.lean`
- **Status**: open · **File**: `ONable.lean` · **Depends on**: T027 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `ONable.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T028] Reductions of orthonormal bases are bases (Bellaïche II.1.12, 'only if')
- **Status**: open · **File**: `Serre.lean` · **Depends on**: CLEANUP-12 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L28.1–L28.2

#### Statement
```lean
theorem linearIndependent_residueFamily_of_isOrthonormalFamily (he : IsOrthonormalFamily R e) :
    LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he.norm_le_one) := by
  sorry

theorem span_residueFamily_eq_top_of_isOrthonormalBasis (he : IsOrthonormalBasis R e) :
    Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he.1.norm_le_one)) = ⊤ := by
  sorry
```
#### Proof sketch
1. `linearIndependent_residueFamily_of_isOrthonormalFamily`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`. Lift `g j` to `a j : unitClosedBall R`
   (`Ideal.Quotient.mk_surjective`, `choose`); then `∑ j ∈ s, g j • residueFamily … j = Submodule.Quotient.mk (∑ j ∈ s, a j • ⟨e j, _⟩)`
   (`Submodule.Quotient.mk_sum`, `Submodule.Quotient.mk_smul`, `residueFamily`), so `hg` says `∑ j ∈ s, a j • ⟨e j, _⟩ ∈ ϖ.ideal • ⊤`
   (`Submodule.Quotient.mk_eq_zero`), i.e. `‖∑ j ∈ s, (a j : R) • e j‖ < 1` by `ϖ.mem_ideal_smul_top_iff_norm_lt_one hM`. By the orthonormal identity
   this sup is `≥ ‖(a i : R)‖`, so `‖(a i : R)‖ < 1`, i.e. `a i ∈ openUnitBallIdeal R = ϖ.ideal` (`mem_openUnitBallIdeal`, `ϖ.ideal_eq_openUnitBallIdeal hR`),
   hence `g i = Ideal.Quotient.mk _ (a i) = 0` (`Ideal.Quotient.eq_zero_iff_mem`).
2. `span_residueFamily_eq_top_of_isOrthonormalBasis`: `eq_top_iff.2 fun x _ ↦ ?_`; `obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x`;
   expand `m = ∑' a i • e i` (`he.exists_hasSum'`) with `‖a i‖ ≤ ‖m‖ ≤ 1`; `F := {i | ‖a i‖ = 1}` is finite (`he.1.tendsto_cofinite_of_hasSum`,
   eventually `‖a i‖ < 1`); with `s := F.toFinset`, the tail `m - ∑ i ∈ s, a i • e i = ∑' i, (if i ∈ s then 0 else a i) • e i` has every term of norm
   `≤ ‖ϖ‖` (for `i ∉ s`, `‖a i‖ < 1` and `hR` give `‖a i‖ ≤ ‖ϖ‖`: a power `‖ϖ‖ ^ n < 1` forces `n ≥ 1`), hence norm `≤ ‖ϖ‖ < 1`
   (`IsUltrametricDist.norm_tsum_le_of_forall_le`, `ϖ.norm_lt_one`), so the tail lies in `ϖ.ideal • ⊤` and `mk ⟨m, hm⟩ = ∑ i ∈ s, mk (a i) • residueFamily … i`
   (`Submodule.Quotient.eq`), an element of the span (`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span ⟨i, rfl⟩`).

#### Mathlib lemmas needed
`linearIndependent_iff'`, `Ideal.Quotient.mk_surjective`, `Submodule.Quotient.{mk_sum, mk_smul, mk_eq_zero, eq, mk_surjective}`, `NormedRing.PseudoUniformizer.{mem_ideal_smul_top_iff_norm_lt_one, ideal_eq_openUnitBallIdeal}` [L0], `NormedRing.mem_openUnitBallIdeal`, `Ideal.Quotient.eq_zero_iff_mem`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `zpow_lt_one_iff_right_of_lt_one₀`-type lemma for `‖ϖ‖ ^ n < 1 → 1 ≤ n`.
#### Sources
[Bel] Lemma II.1.12 l. 2082–2105 ("Then `(e_i)` is an orthonormal basis of `M` if and only if `(ẽ_i)` is a basis of `M̃` … The other direction is easy and left to the reader"); [Col] Prop 1.1.5, second half of the proof l. 158–171 ("la réduction `ā_i` modulo `π_L` de `a_i` est nulle sauf pour un nombre fini de `i` … les `ē_i` forment une famille génératrice … et donc une base"); [RM] §2.3.1 ("the 'only if' direction is the reduction of the sup-norm identity").
#### Generality decision
Hypotheses `hR`, `hM` as in Layer 0 (Bellaïche's II.1.11 and `|M| ⊂ |R|`); `R` a Banach–Tate commutative ring with the `ResidueModule` instances.

### [T029] A family with linearly independent reduction is orthonormal (II.1.12, 'if', the norm identity)
- **Status**: open · **File**: `Serre.lean` · **Depends on**: T028 · **Parallel**: no · **Type**: lemma
- **Leaves**: L29.1

#### Statement
```lean
theorem isOrthonormalFamily_of_linearIndependent_residueFamily (he : ∀ i, ‖e i‖ ≤ 1)
    (hli : LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he)) : IsOrthonormalFamily R e := by
  sorry
```
#### Proof sketch
Prove first `key : ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊`, then `‖e i‖ = 1` is `key {i} 1` with `norm_one`.
For `key`: if `∀ i ∈ s, a i = 0` both sides are `0`. Otherwise pick `i₀ ∈ s` maximising `‖a i‖` (`Finset.exists_max_image`), `a i₀ ≠ 0`, and by `hR`
`‖a i₀‖ = ‖ϖ‖ ^ n`. Scale: `b j := ((ϖ.unit ^ (-n) : Rˣ) : R) * a j`, so `‖b j‖ = ‖ϖ‖ ^ (-n) * ‖a j‖ ≤ 1` with equality at `i₀`
(`IsMultiplicative.norm_mul`, `norm_zpow` for `ϖ.unit`). Let `x := ∑ j ∈ s, b j • e j`; `‖x‖ ≤ 1` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `he j`).
Its reduction `mk ⟨x, _⟩ = ∑ j ∈ s, mk (b j) • residueFamily … j` is nonzero: `mk (b i₀) ≠ 0` because `b i₀ ∉ ϖ.ideal` (`ϖ.mem_ideal_iff`: `‖b i₀‖ = 1 > ‖ϖ‖`)
and `hli` (`linearIndependent_iff'`). Hence `x ∉ ϖ.ideal • ⊤`, so `¬ ‖x‖ < 1` (`mem_ideal_smul_top_iff_norm_lt_one hM`), so `‖x‖ = 1`. Finally
`∑ a j • e j = (ϖ.unit ^ n : R) • x` (`smul_sum`, `mul_smul`, `Units.inv_mul_cancel_left`-type cancellation) has norm `‖ϖ‖ ^ n * 1 = ‖a i₀‖`
(`ϖ.norm_zpow_smul`), which is the sup (`Finset.sup` attained at `i₀`, `Finset.le_sup`/`Finset.sup_le` with the maximality). Convert with `coe_nnnorm`.

#### Mathlib lemmas needed
`Finset.exists_max_image`, `NormedRing.IsMultiplicative.norm_mul` [L0], `NormedRing.PseudoUniformizer.{norm_zpow, norm_zpow_smul, mem_ideal_iff, mem_ideal_smul_top_iff_norm_lt_one}` [L0], `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `linearIndependent_iff'`, `Submodule.Quotient.{mk_sum, mk_smul, mk_eq_zero}`, `Finset.smul_sum`, `smul_smul`, `Finset.le_sup`, `Finset.sup_le`.
#### Sources
[Bel] Lemma II.1.12 l. 2095–2101 ("If `|m| = 1`, then some `a¹_i` has norm `1`, and so does `a_i`, and thus `|m| = sup_i |a_i|`. By replacing `m` by `πⁿ m` for the `n` such that `|m| = |π|^{-n}`, we see that the same result holds for any `m ∈ M`"); [Sch] Prop 10.1 l. 2963–2974 ("We may assume without loss of generality that `a₁ ≠ 0` and that `|a₁| ≥ |a_i|` … the vector `v_{x₁} + (a₂/a₁) v_{x₂} + … lies in `B₁(0)` but not in `B₁⁻(0)`. Hence `‖a₁ v_{x₁} + … + a_m v_{x_m}‖ = |a₁|`"); [Col] l. 150–157.
#### Generality decision
Scaling by the unit `ϖ.unit ^ (-n)` replaces Schneider's division by `a₁` (not available over a ring); `hR` provides `n`.

### [T030] Successive `ϖ`-adic approximation and the lifting of residue bases (II.1.12, 'if')
- **Status**: open · **File**: `Serre.lean` · **Depends on**: T029 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L30.1–L30.2

#### Statement
```lean
theorem exists_hasSum_of_span_residueFamily_eq_top (he : ∀ i, ‖e i‖ ≤ 1)
    (hspan : Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he)) = ⊤) (m : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) m := by
  sorry

theorem isOrthonormalBasis_of_residueFamily (he : ∀ i, ‖e i‖ ≤ 1)
    (hli : LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he))
    (hspan : Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he)) = ⊤) :
    IsOrthonormalBasis R e := by
  sorry
```
#### Proof sketch
1. **One step** (private lemma): `∀ m : M, ‖m‖ ≤ 1 → ∃ (s : Finset I) (a : I → R), (∀ i, ‖a i‖ ≤ 1) ∧ (∀ i ∉ s, a i = 0) ∧ ‖m - ∑ i ∈ s, a i • e i‖ ≤ ‖ϖ‖`:
   `mk ⟨m, _⟩ ∈ span (range (residueFamily …)) = ⊤` gives (`Finsupp.mem_span_range_iff_exists_finsupp`) a finitely supported `c` with
   `c.sum (fun i α ↦ α • residueFamily … i) = mk ⟨m, _⟩`; lift each `c i` to `a i : unitClosedBall R` (`Ideal.Quotient.mk_surjective`, `0` off the support);
   then `m - ∑ (a i : R) • e i ∈ ϖ.ideal • ⊤` (`Submodule.Quotient.eq`, `mk_sum`, `mk_smul`), i.e. its norm is `< 1` (`mem_ideal_smul_top_iff_norm_lt_one hM`),
   hence `≤ ‖ϖ‖` (`hM`: a value `‖ϖ‖ ^ n < 1` has `n ≥ 1`).
2. **Iterate**: `m₀ := m` (first scale `m` into the unit ball with `existsUnique_zpow_norm_smul_mem_Ioc_one` and undo at the end, as Bellaïche does),
   `mₙ₊₁ := ((ϖ.unit⁻¹ : Rˣ) : R) • (mₙ - ∑ i ∈ sₙ, aₙ i • e i)` with `‖mₙ₊₁‖ ≤ 1` (`ϖ.norm_smul`, `ϖ.norm_inv`); by induction
   `m - ∑ i ∈ ⋃ₖ<ₙ sₖ, (∑ k < n, (ϖ.unit ^ k : R) * aₖ i) • e i = (ϖ.unit ^ n : R) • mₙ`, of norm `≤ ‖ϖ‖ ^ n`.
3. **Limit coefficients**: `A i := ∑' k, (ϖ.unit ^ k : R) * aₖ i`, summable in `R` (`‖(ϖ ^ k) * aₖ i‖ ≤ ‖ϖ‖ ^ k`, `summable_geometric_of_lt_one`,
   `Summable.of_norm_bounded`), with `‖A i - ∑ k < n, …‖ ≤ ‖ϖ‖ ^ n` (ultrametric tail bound). `A → 0` cofinitely: given `ε`, choose `K` with `‖ϖ‖ ^ K < ε`;
   outside the finite union of the supports `s₀ ∪ … ∪ s_{K-1}`, `‖A i‖ ≤ ‖ϖ‖ ^ K` (`IsUltrametricDist.norm_tsum_le_of_forall_le`).
4. **The sum**: `(fun i ↦ A i • e i)` is summable (`summable_smul_of_bounded`-type, `‖e i‖ ≤ 1`), and `‖m - ∑' A i • e i‖ ≤ ‖ϖ‖ ^ n` for every `n`
   (write the difference as `(ϖ ^ n) • mₙ + ∑' (Aₙ i - A i) • e i` with the tail bound), hence `= 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`).
5. `isOrthonormalBasis_of_residueFamily`: `⟨ϖ.isOrthonormalFamily_of_linearIndependent_residueFamily hR hM he hli, ?_⟩`; density from
   `exists_hasSum_of_span_residueFamily_eq_top` exactly as in T020 step 3 (`mem_closure_of_tendsto`).
Pattern: [SRC] `07_Residue.lean` `exists_expansion_of_residue_approx` (field case, same induction).

#### Mathlib lemmas needed
`Finsupp.mem_span_range_iff_exists_finsupp`, `Ideal.Quotient.mk_surjective`, `Submodule.Quotient.{eq, mk_sum, mk_smul}`, `NormedRing.PseudoUniformizer.{mem_ideal_smul_top_iff_norm_lt_one, norm_smul, norm_inv, norm_zpow_smul, existsUnique_zpow_norm_smul_mem_Ioc_one}` [L0], `summable_geometric_of_lt_one`, `Summable.of_norm_bounded`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `mem_closure_of_tendsto`.
#### Sources
[Bel] Lemma II.1.12 l. 2088–2095 ("Choosing lifts `a¹_i` of the `α_i` in `R⁰`, we have `m − ∑ a¹_i e_i = π m₁` with `m₁ ∈ M⁰`. Applying the same result to `m₁` … by induction `m − ∑ aⁿ_i e_i = πⁿ mₙ` … the sequence `(aⁿ_i)` satisfies `|aⁿ_i − aⁿ⁺¹_i| ≤ |π|ⁿ`, hence is Cauchy, and therefore converges to an element `a_i ∈ R⁰` … One has `m = ∑ a_i e_i`"); [Col] Prop 1.1.5 l. 136–149 (the same recursion `x_{n+1} = π⁻¹(x_n − s(x_n))`); [RM] §2.3.1.
#### Generality decision
Over a Banach–Tate commutative ring with `hR`, `hM`; the coefficients converge because `R` is complete. The longest ticket of the board: split sub-tickets per A2 (the one-step lemma, the iteration, the limit) when executing.

### [CLEANUP-13] Run `/cleanup` on `Serre.lean`
- **Status**: open · **File**: `Serre.lean` · **Depends on**: T028, T029, T030 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Serre.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T031] Serre's theorem, ring form
- **Status**: open · **File**: `Serre.lean` · **Depends on**: CLEANUP-13 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L31.1–L31.4

#### Statement
```lean
theorem free_residueModule_of_isONable (h : IsONable R M) :
    Module.Free ϖ.ResidueRing (ϖ.ResidueModule M) := by
  sorry

theorem isONable_of_free_residueModule [Module.Free ϖ.ResidueRing (ϖ.ResidueModule M)] :
    IsONable R M := by
  sorry

theorem isPotentiallyONable_of_forall_free
    (hfree : ∀ (N : Type v) [AddCommGroup N] [Module ϖ.ResidueRing N],
      Module.Free ϖ.ResidueRing N) : IsPotentiallyONable R M := by
  sorry

theorem isPotentiallyONable_of_isField_residueRing (hF : IsField ϖ.ResidueRing) :
    IsPotentiallyONable R M := by
  sorry
```
#### Proof sketch
1. `free_residueModule_of_isONable`: `obtain ⟨I, _, _, ⟨Φ⟩⟩ := h`; classical; `he := Φ.isOrthonormalBasis_symm_single` (T021);
   `Module.Free.of_basis (Module.Basis.mk (ϖ.linearIndependent_residueFamily_of_isOrthonormalFamily hR hM he.1) (by rw [ϖ.span_residueFamily_eq_top_of_isOrthonormalBasis hR hM he]))`.
2. `isONable_of_free_residueModule`: `b := Module.Free.chooseBasis ϖ.ResidueRing (ϖ.ResidueModule M)` (index `Module.Free.ChooseBasisIndex … : Type v`);
   `choose e he using fun i ↦ Submodule.Quotient.mk_surjective _ (b i)` gives `e i : Submodule.unitClosedBall R M`; set `e' i := (e i : M)`, `‖e' i‖ ≤ 1`
   (`Submodule.mem_unitClosedBall`); `residueFamily ϖ e' _ = b` by `funext` (`he`); so `b.linearIndependent` and `b.span_eq` give the hypotheses of
   `isOrthonormalBasis_of_residueFamily`, and `IsOrthonormalBasis.isONable` (T023) concludes.
3. `isPotentiallyONable_of_forall_free`: `haveI := ϖ.isBoundedSMul_rescaled M hR`; `hM' : ∀ m : ϖ.Rescaled M, m ≠ 0 → ∃ n, ‖m‖ = ‖ϖ‖ ^ n := fun m hm ↦ ϖ.exists_norm_rescaled_eq_zpow hm`;
   `haveI := hfree (ϖ.ResidueModule (ϖ.Rescaled M))`; `h₁ : IsONable R (ϖ.Rescaled M) := ϖ.isONable_of_free_residueModule hR hM'`; the identity
   `ϖ.toRescaled M : M ≃ₗ[R] ϖ.Rescaled M` is a `≃L`: continuity from the bounds `‖m‖ ≤ ‖toRescaled m‖` (`norm_le_norm_toRescaled`) and
   `‖toRescaled m‖ ≤ ‖ϖ‖⁻¹ * ‖m‖` (from `norm_mul_norm_toRescaled_lt`, `ϖ.norm_pos`), via `AddMonoidHomClass.continuous_of_bound`; build
   `{ toLinearEquiv := ϖ.toRescaled M, continuous_toFun := _, continuous_invFun := _ }` and finish with `h₁.isPotentiallyONable.of_continuousLinearEquiv e.symm`.
4. `isPotentiallyONable_of_isField_residueRing`: `ϖ.isPotentiallyONable_of_forall_free hR fun N _ _ ↦ by letI := hF.toField; exact Module.Free.of_divisionRing _ _`.

#### Mathlib lemmas needed
`Module.Free.of_basis`, `Module.Basis.mk`, `Module.Free.chooseBasis`, `Module.Basis.{linearIndependent, span_eq}`, `Submodule.Quotient.mk_surjective`, `NormedRing.PseudoUniformizer.{isBoundedSMul_rescaled, exists_norm_rescaled_eq_zpow, toRescaled, norm_le_norm_toRescaled, norm_mul_norm_toRescaled_lt, norm_pos}` [L0], `AddMonoidHomClass.continuous_of_bound`, `IsField.toField`, `Module.Free.of_divisionRing`.
#### Sources
[RM] §2.3.2 ("`M` is orthonormalisable if and only if `M̃` is a free `R̃`-module; and every Banach `R`-module is potentially orthonormalisable as soon as `R̃` has the property that all its modules are free — in particular when `R̃` is a field"); [Bel] Lemma II.1.12 l. 2086–2087 ("In particular, `M` is orthonormalizable if and only if `M̃` is free over `R̃`") and Thm II.1.13 l. 2108–2114 (the equivalent norm `|m|' = inf_{r ∈ p^ℤ, r ≥ |m|} r`); [RM] §0.3.3 (the rescaled norm).
#### Generality decision
The rescaled module needs `hR` for its `IsBoundedSMul` (Layer 0); `hM` is only needed for the on-the-nose statements.

### [CLEANUP-ALL-2] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: T031, CLEANUP-12 · **Parallel**: no · **Type**: cleanup
- **Description**: Pre-milestone sweep before M2. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T032] MILESTONE M2 — Serre's theorem over a discretely valued field
- **Status**: open · **File**: `Serre.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: milestone
- **Leaves**: L32.1–L32.4

#### Statement
```lean
theorem NormedField.exists_pseudoUniformizer_forall_exists_norm_eq_zpow
    [Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))] :
    ∃ ϖ : PseudoUniformizer K, ∀ r : K, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : K)‖ ^ n := by
  sorry

theorem NormedRing.PseudoUniformizer.isField_residueRing (ϖ : PseudoUniformizer K)
    (hK : ∀ r : K, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : K)‖ ^ n) : IsField ϖ.ResidueRing := by
  sorry

theorem Module.isPotentiallyONable_of_isRankOneDiscrete : IsPotentiallyONable K M := by
  sorry

theorem Module.isONable_iff_forall_exists_norm_eq : IsONable K M ↔ ∀ m : M, ∃ k : K, ‖m‖ = ‖k‖ := by
  sorry
```
#### Proof sketch
1. `exists_pseudoUniformizer_forall_exists_norm_eq_zpow`: `v := NormedField.valuation (K := K)` with `v x = ‖x‖₊` (`NormedField.valuation_apply`);
   `obtain ⟨π, hπ⟩ := Valuation.IsRankOneDiscrete.generator_mem_range K v` (`‖π‖₊ = generator v`), `π ≠ 0` (`generator_ne_zero`), `‖π‖ < 1`
   (`generator_lt_one`); `ϖ := ⟨Units.mk0 π hπ0, NormedRing.isMultiplicative_of_normMulClass _, by simpa using hlt⟩`; for `r ≠ 0`,
   [NP] `Valuation.IsRankOneDiscrete.exists_zpow_generator_eq (v := v) (by simpa)` gives `n` with `‖r‖₊ = generator v ^ n = ‖π‖₊ ^ n`, and
   `NNReal.coe_zpow`/`coe_nnnorm` turn it into `‖r‖ = ‖π‖ ^ n`.
2. `isField_residueRing`: `ϖ.ideal = openUnitBallIdeal K` (`ϖ.ideal_eq_openUnitBallIdeal hK`) `= IsLocalRing.maximalIdeal _` (`NormedRing.maximalIdeal_unitClosedBall`),
   which is maximal (`IsLocalRing.maximalIdeal.isMaximal`); `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1` after rewriting.
3. `isPotentiallyONable_of_isRankOneDiscrete`: `obtain ⟨ϖ, hK⟩ := NormedField.exists_pseudoUniformizer_forall_exists_norm_eq_zpow K`;
   `exact ϖ.isPotentiallyONable_of_isField_residueRing hK (ϖ.isField_residueRing hK)`.
4. `isONable_iff_forall_exists_norm_eq`: (⟹) `obtain ⟨I, _, _, ⟨Φ⟩⟩`; `‖m‖ = ‖Φ m‖`; `rcases isEmpty_or_nonempty I` — empty: `Φ m = 0`, take `k := 0`;
   nonempty: `obtain ⟨i, hi⟩ := exists_norm_apply_eq_norm (Φ m)`, take `k := Φ m i`. (⟸) with `ϖ, hK` as in 3, `hM : ∀ m ≠ 0, ∃ n, ‖m‖ = ‖ϖ‖ ^ n`
   from `h m` and `hK` (`k ≠ 0` since `‖m‖ ≠ 0`); `letI := (ϖ.isField_residueRing hK).toField; haveI := Module.Free.of_divisionRing ϖ.ResidueRing (ϖ.ResidueModule M)`;
   `ϖ.isONable_of_free_residueModule hK hM`.

#### Mathlib lemmas needed
`NormedField.valuation_apply`, `Valuation.IsRankOneDiscrete.{generator_mem_range, generator_lt_one, generator_ne_zero}`, `Valuation.IsRankOneDiscrete.exists_zpow_generator_eq` [NP], `NormedRing.isMultiplicative_of_normMulClass` [L0], `Units.mk0`, `NNReal.coe_zpow`, `NormedRing.PseudoUniformizer.ideal_eq_openUnitBallIdeal` [L0], `NormedRing.maximalIdeal_unitClosedBall` [L0], `IsLocalRing.maximalIdeal.isMaximal`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient`, `IsField.toField`, `Module.Free.of_divisionRing`, `exists_norm_apply_eq_norm` (T002).
#### Sources
[RM] §2.3.3 ("Every Banach space over a discretely valued nonarchimedean field `K` is potentially orthonormalisable, and it is orthonormalisable on the nose if and only if its norm takes values in `‖K‖`"); [Sch] Prop 10.1 l. 2948–2951 and its proof l. 2952–2960 ("According to Lemma 1.4 we have `|K×| = r^ℤ` … `k := o/m` denote the residue class field"), Remark 10.2 l. 3003–3006; [Sch] Lemma 1.4 l. 291–312; [Bel] Thm II.1.13 l. 2108–2114; convention 8 (`IsRankOneDiscrete`).
#### Generality decision
`[Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))]` is the roadmap's convention 8; the uniformiser comes from Mathlib's generator plus [NP]'s `exists_zpow_generator_eq` (seam S2).

### [T033] The index set of `C₀(I, K)` is an invariant (Schneider, Lemma 10.3)
- **Status**: open · **File**: `Serre.lean` · **Depends on**: T032 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L33.1–L33.3

#### Statement
```lean
theorem finite_of_continuousLinearEquiv [Finite I] (e : C₀(I, K) ≃L[K] C₀(J, K)) : Finite J := by
  sorry

theorem cardinal_mk_le_of_continuousLinearEquiv [Infinite I] (e : C₀(I, K) ≃L[K] C₀(J, K)) :
    Cardinal.mk J ≤ Cardinal.mk I := by
  sorry

theorem nonempty_equiv_of_continuousLinearEquiv (e : C₀(I, K) ≃L[K] C₀(J, K)) :
    Nonempty (I ≃ J) := by
  sorry
```
#### Proof sketch
1. `finite_of_continuousLinearEquiv`: `Fintype.ofFinite I`; `FiniteDimensional K C₀(I, K)` from `(piEquiv (R := K)).toLinearEquiv.symm` and
   `Module.Finite.of_surjective`/`LinearEquiv.finiteDimensional`; transport along `e.toLinearEquiv`; the family `fun j ↦ single j (1 : K)` is linearly
   independent (`isOrthonormalBasis_single.1.linearIndependent`), hence `Finite J` (`LinearIndependent.finite` / `Module.Finite.finite_of_linearIndependent`).
2. `cardinal_mk_le_of_continuousLinearEquiv`: show `Set.univ ⊆ ⋃ i : I, {j | e (single i 1) j ≠ 0}`: for `j`, if `e (single i 1) j = 0` for all `i`, then
   for every `f`, `(e f) j = 0` — write `e f = ∑' i, f i • e (single i 1)` (`hasSum_smul_apply_single (e : C₀(I, K) →L[K] C₀(J, K)) f`, map by `evalCLM K j`)
   — contradicting surjectivity at `single j 1`. Then `Cardinal.mk J = #(univ) ≤ #(⋃ …) ≤ Cardinal.sum fun i ↦ #(supp i)` (`Cardinal.mk_iUnion_le_sum_mk`)
   `≤ #I * ℵ₀` (`Cardinal.sum_le_iSup`-type bound with `#(supp i) ≤ ℵ₀` from `countable_support` and `Cardinal.mk_le_aleph0`) `= #I`
   (`Cardinal.mul_eq_left (Cardinal.aleph0_le_mk I) le_rfl? ` with `ℵ₀ ≤ #I` from `Infinite I` and `ℵ₀ ≠ 0`).
3. `nonempty_equiv_of_continuousLinearEquiv`: `rcases finite_or_infinite I`. Finite: `haveI := finite_of_continuousLinearEquiv e`, `Fintype` both; the finranks
   agree (`LinearEquiv.finrank_eq e.toLinearEquiv`, `Module.finrank_pi` through `piEquiv`), so `Fintype.card I = Fintype.card J` and `Fintype.equivOfCardEq`.
   Infinite: `Infinite J` (otherwise the finite case for `e.symm` makes `I` finite); `le_antisymm (cardinal_mk_le_of_continuousLinearEquiv e.symm) (cardinal_mk_le_of_continuousLinearEquiv e)`
   and `Cardinal.eq.1`.

#### Mathlib lemmas needed
`Fintype.ofFinite`, `LinearEquiv.finiteDimensional`, `LinearIndependent.finite` (or `Module.Finite.finite_of_linearIndependent`), `hasSum_smul_apply_single` (T006), `Cardinal.{mk_iUnion_le_sum_mk, sum_le_iSup, mk_le_aleph0, mul_eq_left, aleph0_le_mk, eq}`, `countable_support` (T002), `finite_or_infinite`, `LinearEquiv.finrank_eq`, `Module.finrank_pi`, `Fintype.equivOfCardEq`.
#### Sources
[Sch] Lemma 10.3 l. 3007–3028 ("If one of the sets is finite then already for algebraic reasons the other set has to be finite of the same cardinality … The sets `Y_x := {y ∈ Y : f(1_x)(y) ≠ 0}` … each `Y_x` is finite or countable … for any `y ∈ Y` there is an `x ∈ X` such that `y ∈ Y_x`. If not all the `f(1_x)` would be contained in the complete and hence closed vector subspace `c₀(Y∖{y})` … It follows that `|Y| ≤ |⋃ Y_x| ≤ |ℕ| · |X| = |X|`"); [RM] §2.3.4.
#### Generality decision
Over any complete nonarchimedean nontrivially normed `K` (Schneider assumes no discreteness here); `I`, `J` in one universe for `Cardinal.mk`.

### [CLEANUP-14] Run `/cleanup` on `Serre.lean`
- **Status**: open · **File**: `Serre.lean` · **Depends on**: T033 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Serre.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T034] The distance step of Schneider's Proposition 10.4
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: CLEANUP-14 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L34.1–L34.2

#### Statement
```lean
theorem Submodule.exists_add_mem_forall_mul_norm_le (U : Submodule K V) (hU : IsClosed (U : Set V))
    {w : V} (hw : w ∉ U) {r : ℝ} (hr : r < 1) :
    ∃ u₀ ∈ U, ∀ u ∈ U, r * ‖w + u₀‖ ≤ ‖w + u₀ + u‖ := by
  sorry

theorem norm_smul_add_ge_mul_max (U : Submodule K V) {v : V} {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1)
    (hv : ∀ u ∈ U, r * ‖v‖ ≤ ‖v + u‖) (a : K) {u : V} (hu : u ∈ U) :
    r * max ‖a • v‖ ‖u‖ ≤ ‖a • v + u‖ := by
  sorry
```
#### Proof sketch
1. `exists_add_mem_forall_mul_norm_le`: `d := Metric.infDist w (U : Set V)`; `0 < d` by `(hU.notMem_iff_infDist_pos ⟨0, U.zero_mem⟩).1 hw`.
   If `r ≤ 0`: `⟨0, U.zero_mem, fun u hu ↦ (mul_nonpos_of_nonpos_of_nonneg? …).trans (norm_nonneg _)⟩`. If `0 < r`: `d < d / r` (`hr`, `lt_div_iff₀`),
   so `Metric.infDist_lt_iff ⟨0, U.zero_mem⟩` gives `y ∈ U` with `dist w y < d / r`; take `u₀ := -y` (`U.neg_mem`); for `u ∈ U`:
   `‖w + u₀ + u‖ = dist w (y - u)` (`dist_eq_norm`, `sub_eq_add_neg`) `≥ d` (`Metric.infDist_le_dist_of_mem (U.sub_mem hy hu)`), while
   `r * ‖w + u₀‖ = r * dist w y < d` (`dist_eq_norm`, `mul_lt_of_lt_div`). Combine.
2. `norm_smul_add_ge_mul_max`: `by_cases ha : a = 0`: then `‖0 + u‖ = ‖u‖` and `r * max 0 ‖u‖ = r * ‖u‖ ≤ ‖u‖` (`mul_le_of_le_one_left`).
   Otherwise `‖a • v + u‖ = ‖a‖ * ‖v + a⁻¹ • u‖` (`smul_add`, `smul_smul`, `norm_smul`, `inv_mul_cancel₀`) `≥ ‖a‖ * (r * ‖v‖) = r * ‖a • v‖`
   (`hv _ (U.smul_mem _ hu)`); if `‖a • v‖ ≠ ‖u‖` then `‖a • v + u‖ = max ‖a • v‖ ‖u‖` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) and
   `r * max ≤ max` (`mul_le_of_le_one_left`); if equal, `max = ‖a • v‖` and the previous bound applies.

#### Mathlib lemmas needed
`Metric.infDist`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_lt_iff`, `Metric.infDist_le_dist_of_mem`, `lt_div_iff₀`, `mul_lt_of_lt_div`, `dist_eq_norm`, `Submodule.{neg_mem, sub_mem, smul_mem, zero_mem}`, `norm_smul`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `mul_le_of_le_one_left`.
#### Sources
[Sch] Prop 10.4 proof l. 3047–3056 ("Fixing some `v ∈ Vₙ ∖ Vₙ₋₁` we therefore have `inf{‖v + w‖ : w ∈ Vₙ₋₁} > 0`. There consequently exists a vector `w' ∈ Vₙ₋₁` such that `rₙ/rₙ₊₁ ≤ inf{‖v + w‖ : w ∈ Vₙ₋₁}/‖v + w'‖ ≤ 1`") and l. 3057–3068 ("`‖a vₙ + w‖ ≥ (rₙ/rₙ₊₁) max(‖a vₙ‖, ‖w‖)` … If `‖a vₙ‖ = ‖w‖` this is a consequence of the previous inequality; if `‖a vₙ‖ ≠ ‖w‖` this follows from `‖a vₙ + w‖ = max(‖a vₙ‖, ‖w‖)`").
#### Generality decision
Field scalars (division by `a`), `V` ultrametric; closedness of `U` as an explicit hypothesis (it will be a finite-dimensional subspace).

### [T035] The `t`-orthogonal sequence (Schneider 10.4 (a)–(d)) and the finite-dimensional case
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: T034 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L35.1–L35.2

#### Statement
```lean
theorem Module.IsCountableType.exists_isTOrthogonalFamily_nat (hV : IsCountableType K V)
    (hfin : ¬ FiniteDimensional K V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ v : ℕ → V, (∀ n, ‖v n‖ ≤ 1) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ ‖v n‖) ∧
      IsTOrthogonalFamily K t v ∧ Dense (Submodule.span K (Set.range v) : Set V) := by
  sorry

theorem Module.exists_isTOrthogonalFamily_fin_of_finiteDimensional [FiniteDimensional K V] {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (n : ℕ) (v : Fin n → V), IsTOrthogonalFamily K t v ∧
      Submodule.span K (Set.range v) = ⊤ := by
  sorry
```
#### Proof sketch
1. **A linearly independent enumeration.** `obtain ⟨s, hs, hd⟩ := hV`; `obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent K s` (`b ⊆ s`, `span b = span s`,
   `LinearIndependent K ((↑) : b → V)`); `b` is countable (`hs.mono hbs`) and infinite (if finite, `span b` is finite-dimensional, closed
   (`Submodule.closed_of_finiteDimensional`) and dense, so `= ⊤` and `FiniteDimensional K V`, contradicting `hfin`); so `Nonempty (Denumerable b)`
   (`Set.countable_infinite_iff_nonempty_denumerable`) and `u : ℕ → V := fun n ↦ ((Denumerable.eqv b).symm n : V)` is injective with range `b`,
   `LinearIndependent K u` (`hli.comp _ (Equiv.injective _)`).
2. **The chain.** `Vₙ := Submodule.span K (u '' Set.Iio n)`; finite-dimensional hence closed; `u n ∉ Vₙ` (`LinearIndependent.notMem_span_image`, `Nontrivial K`).
3. **The sequence.** `rₖ := 1 - (1 - t) / (k + 1)` (`r₀ = t`, increasing, `< 1`), `ρₖ := rₖ / rₖ₊₁ ∈ (0, 1)`; `vₙ := u n + u₀ n` where `u₀ n ∈ Vₙ` is
   given by `Submodule.exists_add_mem_forall_mul_norm_le Vₙ _ (hu n) (ρₙ < 1)` (no recursion: `Vₙ` depends on `u`, not on earlier `v`'s).
   (a) `span (v '' Iio n) = Vₙ` by induction (`Submodule.span_insert`-style, each `v k ∈ u k + V_k`), and `v n ∉ Vₙ`.
   (b') `∀ a x, x ∈ Vₙ → ρₙ * max ‖a • vₙ‖ ‖x‖ ≤ ‖a • vₙ + x‖` (T034.2).
4. **(c) by induction on `n`:** `‖∑ i ≤ n, aᵢ • vᵢ‖ ≥ max_{i ≤ n} (rᵢ / rₙ₊₁) ‖aᵢ • vᵢ‖`: split off the top term, apply (b') with `x = ∑ i < n …` (in `Vₙ`),
   use the induction hypothesis and `ρₙ * (rᵢ / rₙ) = rᵢ / rₙ₊₁`. Since `rᵢ / rₙ₊₁ ≥ r₀ = t`, this is `IsTOrthogonalFamily K t v` (for a `Finset`
   `s`, extend `a` by `0` outside `s` and take `n := s.sup id`).
5. **(d) scaling.** `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := K)`; for each `n`, `existsUnique_zpow_norm_smul_mem_Ioc_one` gives `cₙ := ϖ.unit ^ mₙ`
   with `‖cₙ • vₙ‖ ∈ Ioc ‖ϖ‖ 1`; `v' n := cₙ • vₙ`: `t`-orthogonal (`IsTOrthogonalFamily.smul`), `‖v' n‖ ≤ 1`, `δ := ‖ϖ‖ > 0` bounds below, and
   `span (range v') = span (range v) = span (range u) = span b = span s` is dense (`Submodule.span_smul_eq`-type: scaling by units does not change spans).
6. `exists_isTOrthogonalFamily_fin_of_finiteDimensional`: the same construction with `u := FiniteDimensional.finBasis K V` (or `Module.Basis.ofVectorSpace`
   re-indexed by `Fin n`), steps 2–5 for `n < finrank`, and `span (range v) = ⊤` from (a).

#### Mathlib lemmas needed
`exists_linearIndependent`, `Set.Countable.mono`, `Submodule.closed_of_finiteDimensional`, `Set.countable_infinite_iff_nonempty_denumerable`, `Denumerable.eqv`, `LinearIndependent.comp`, `LinearIndependent.notMem_span_image`, `Submodule.span_insert`, `Finset.sup`, `NormedRing.IsTate.exists_pseudoUniformizer`, `NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc_one` [L0], `IsTOrthogonalFamily.smul` (T017), `FiniteDimensional.finBasis`, `Dense.mono`.
#### Sources
[Sch] Prop 10.4 proof l. 3033–3083 ("Choose an ascending sequence of vector subspaces `{0} = V₀ ⊆ V₁ ⊆ … ` … `dim_K Vₙ = n` … `⋃ Vₙ` is dense in `V`. In addition we fix an increasing sequence of real numbers `0 < r = r₁ < r₂ < … < rₙ < … < 1`. We want to inductively construct a sequence of vectors `(vₙ)` … (a) `{v₁, …, vₙ}` is a `K`-basis of `Vₙ` … (b) `‖vₙ + w‖ ≥ (rₙ/rₙ₊₁)‖vₙ‖` … We inductively deduce … (c) `‖∑ aᵢvᵢ‖ ≥ r · max(‖a₁v₁‖, …, ‖aₙvₙ‖)` … We therefore may assume that `ε ≤ ‖vₙ‖ ≤ 1` … (d) `‖∑ aᵢvᵢ‖ ≥ r · max(|a₁|, …, |aₙ|)`"); [RM] §2.4.1–2.4.2.
#### Generality decision
The second-longest ticket; split per A2 into (i) the enumeration, (ii) the chain + (a), (iii) the induction (c), (iv) the scaling. Any complete nonarchimedean `K` (no discreteness).

### [CLEANUP-ALL-3] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: T035, CLEANUP-14 · **Parallel**: no · **Type**: cleanup
- **Description**: Pre-milestone sweep before M3. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T036] MILESTONE M3 — Schneider's Proposition 10.4 and potential orthonormalisability of countable type
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: CLEANUP-ALL-3 · **Parallel**: no · **Type**: milestone
- **Leaves**: L36.1–L36.2

#### Statement
```lean
theorem Module.IsCountableType.exists_continuousLinearEquiv_nat (hV : IsCountableType K V)
    (hfin : ¬ FiniteDimensional K V) : Nonempty (V ≃L[K] C₀(ℕ, K)) := by
  sorry

theorem Module.IsCountableType.isPotentiallyONable (hV : IsCountableType K V) :
    IsPotentiallyONable K V := by
  sorry
```
#### Proof sketch
1. `exists_continuousLinearEquiv_nat`: `obtain ⟨v, hv1, ⟨δ, hδ, hvδ⟩, hvt, hdense⟩ := hV.exists_isTOrthogonalFamily_nat hfin (t := 2⁻¹) (by norm_num) (by norm_num)`;
   `f := ofBounded K v ⟨1, hv1⟩`; **lower bound** `2⁻¹ * δ * ‖a‖ ≤ ‖f a‖`: for a finite `s` and `i ∈ s`, `2⁻¹ * ‖a i • v i‖ ≤ ‖∑ j ∈ s, a j • v j‖`
   and `δ * ‖a i‖ ≤ ‖a i • v i‖` (`norm_smul`), hence `2⁻¹ * δ * ‖a i‖ ≤ ‖∑ …‖`; pass to the limit along the partial sums of `hasSum_ofBounded`
   (`le_of_tendsto`, `eventually_ge_atTop {i}`), getting the bound with `‖a i‖` for every `i`, then `Real.iSup_le`/`norm_eq_iSup`.
   **Injective and closed range**: `AntilipschitzWith.of_le_mul_dist` (constant `(2⁻¹ * δ)⁻¹`) then `AntilipschitzWith.isClosed_range` with
   `f.uniformContinuous` (`CompleteSpace C₀(ℕ, K)` from `CompleteSpace K`). **Dense range**: `range f ⊇ span (range v)` (`v n = f (single n 1)`,
   `Submodule.span_le`), so `closure (range f) = univ` (`Dense.mono`). Hence `range f = univ` (`IsClosed.closure_eq`), `Bijective f`, and
   `(ContinuousLinearMap.Ultra.continuousLinearEquivOfBijective f ⟨inj, surj⟩).symm`.
2. `isPotentiallyONable`: `by_cases hfin : FiniteDimensional K V`: then `n := finrank K V`, `V ≃L[K] (Fin n → K)` (`ContinuousLinearEquiv.ofFinrankEq`,
   `Module.finrank_fin_fun`), `(Fin n → K) ≃ₗᵢ C₀(Fin n, K)` (`piEquiv.symm`), reindex to `ULift.{v} (Fin n)` (`reindex Equiv.ulift.symm`);
   otherwise step 1 and reindex to `ULift.{v} ℕ`.

#### Mathlib lemmas needed
`ofBounded`, `hasSum_ofBounded` (T007), `norm_smul`, `le_of_tendsto`, `Filter.eventually_ge_atTop`, `AntilipschitzWith.of_le_mul_dist`, `AntilipschitzWith.isClosed_range`, `ContinuousLinearMap.uniformContinuous`, `Dense.mono`, `IsClosed.closure_eq`, `ContinuousLinearMap.Ultra.continuousLinearEquivOfBijective` [L1], `ContinuousLinearEquiv.ofFinrankEq`, `Module.finrank_fin_fun`, `piEquiv`, `reindex`, `Equiv.ulift`.
#### Sources
[Sch] Prop 10.4 l. 3029–3031 and proof l. 3084–3101 ("from the universal property of the Banach space `c₀(ℕ)` we obtain a continuous linear map `f : c₀(ℕ) → V` such that `f(1ₙ) = vₙ` … `‖f()‖ ≥ r · ‖‖_∞` … This means that `f` induces a topological isomorphism between `c₀(ℕ)` and `im(f)`. In particular, `im(f)` is complete and hence closed in `V`. On the other hand `im(f)`, by (a), is dense in `V`. Hence `im(f) = V`"); [RM] §2.4.1 ("Hence such a space is potentially orthonormalisable over any `K`").
#### Generality decision
Any complete nonarchimedean `K`; the finite-dimensional case is Mathlib's `ofFinrankEq` (Schneider's Prop 4.13).

### [CLEANUP-15] Run `/cleanup` on `CountableType.lean`
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: T034, T035, T036 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `CountableType.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T037] Quotients, complements and closed subspaces of spaces of countable type (Schneider 10.5)
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: CLEANUP-15, CLEANUP-12 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L37.1–L37.5

#### Statement
```lean
theorem Module.IsCountableType.quotient (hV : IsCountableType K V) (U : Submodule K V)
    [IsClosed (U : Set V)] : IsCountableType K (V ⧸ U) := by
  sorry

theorem Submodule.closedComplemented_of_hasPr_quotient (U : Submodule K V) [IsClosed (U : Set V)]
    (h : HasPr K (V ⧸ U)) : U.ClosedComplemented := by
  sorry

theorem Submodule.closedComplemented_of_isRankOneDiscrete
    [Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))] (U : Submodule K V)
    [IsClosed (U : Set V)] : U.ClosedComplemented := by
  sorry

theorem Submodule.closedComplemented_of_isCountableType (hV : IsCountableType K V)
    (U : Submodule K V) [IsClosed (U : Set V)] : U.ClosedComplemented := by
  sorry

theorem Module.IsCountableType.submodule (hV : IsCountableType K V) (U : Submodule K V)
    [IsClosed (U : Set V)] : IsCountableType K U := by
  sorry
```
#### Proof sketch
1. `quotient`: `obtain ⟨s, hs, hd⟩ := hV`; `⟨U.mkQ '' s, hs.image _, ?_⟩`; `Submodule.span K (U.mkQ '' s) = (Submodule.span K s).map U.mkQ` (`Submodule.span_image`)
   and `DenseRange.dense_image (U.mkQ_surjective.denseRange) continuous_quot_mk hd`.
2. `closedComplemented_of_hasPr_quotient`: `π : V →L[K] V ⧸ U := ⟨U.mkQ, continuous_quot_mk⟩`, surjective (`U.mkQ_surjective`);
   `obtain ⟨s, hs⟩ := h.exists_lift π hsurj (ContinuousLinearMap.id K (V ⧸ U))` (instances: `Submodule.Quotient.{normedAddCommGroup, normedSpace, completeSpace}`
   and Layer 0's `Submodule.Quotient.instIsUltrametricDist`); `ContinuousLinearMap.closedComplemented_ker_of_rightInverse π s (fun y ↦ congrArg (· y) hs)`
   and `LinearMap.ker π = U` (`Submodule.ker_mkQ`).
3. `closedComplemented_of_isRankOneDiscrete`: `closedComplemented_of_hasPr_quotient U (isPotentiallyONable_of_isRankOneDiscrete (V ⧸ U)).hasPr`.
4. `closedComplemented_of_isCountableType`: `closedComplemented_of_hasPr_quotient U (hV.quotient U).isPotentiallyONable.hasPr`.
5. `submodule`: `obtain ⟨P, hP⟩ := closedComplemented_of_isCountableType hV U` (`P : V →L[K] U`, `P u = u` on `U`), so `P` is surjective and `LinearMap.ker P` is closed;
   `hV.quotient (LinearMap.ker P)` is of countable type, and `V ⧸ ker P ≃L[K] U` by Layer 1's `quotKerEquivRangeL` (range `P = ⊤`, `LinearMap.range_eq_top.2`)
   composed with `Submodule.topEquiv`; transport with a small helper `IsCountableType.of_continuousLinearEquiv` (image of the countable set, `Submodule.span_image`, `DenseRange.dense_image`).

#### Mathlib lemmas needed
`Submodule.span_image`, `DenseRange.dense_image`, `Submodule.mkQ_surjective`, `continuous_quot_mk`, `Submodule.ker_mkQ`, `ContinuousLinearMap.closedComplemented_ker_of_rightInverse`, `Submodule.Quotient.{normedAddCommGroup, normedSpace, completeSpace}`, `Submodule.Quotient.instIsUltrametricDist` [L0], `ContinuousLinearMap.Ultra.quotKerEquivRangeL` [L1], `LinearMap.range_eq_top`, `Submodule.topEquiv`.
#### Sources
[Sch] Prop 10.5 l. 3120–3137 ("Let `V` be a `K`-Banach space and suppose that (a) `K` is discretely valued or (b) `V` contains a dense vector subspace of countable dimension; then every closed vector subspace `U ⊆ V` is complemented. Proof: By Prop. 8.3 the quotient `V/U` again is a Banach space which in case (b) contains a vector subspace of countable dimension. It therefore follows from Prop. 10.1 and Prop. 10.4 that … `g : V/U ≅ c₀(X)` … The continuous linear map `f ∘ g : V/U → V` then is a section of the projection map … and `P := (id_V − f ∘ g ∘ pr)` is a continuous projector onto `U`"); [RM] §2.4.3; E25 (closed subspaces via complementation).
#### Generality decision
The lift of the identity replaces Schneider's explicit construction through `c₀(X)` (it is the lifting property of (Pr), T026). `IsClosed U` is an instance argument because Mathlib's quotient norm needs it (seam S4).

### [CLEANUP-16] Run `/cleanup` on `CountableType.lean`
- **Status**: open · **File**: `CountableType.lean` · **Depends on**: T037 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `CountableType.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T038] Matrix coefficients: columns, bounds, extensionality, the action in coordinates
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: CLEANUP-3, CLEANUP-6 · **Parallel**: yes (parallel with the Orthogonal/ONable/Serre chain) · **Type**: lemmas
- **Leaves**: L38.1–L38.4

#### Statement
```lean
theorem tendsto_matrixCoeff_column (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) :
    Tendsto (fun i ↦ matrixCoeff u i j) cofinite (𝓝 0) := by
  sorry

theorem norm_matrixCoeff_le [NormOneClass R] [IsTate R] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I)
    (j : J) : ‖matrixCoeff u i j‖ ≤ ‖u‖ := by
  sorry

theorem ext_matrixCoeff {u v : C₀(J, R) →L[R] C₀(I, R)}
    (h : ∀ i j, matrixCoeff u i j = matrixCoeff v i j) : u = v := by
  sorry

theorem hasSum_matrixCoeff_mul (u : C₀(J, R) →L[R] C₀(I, R)) (f : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ matrixCoeff u i j * f j) (u f i) := by
  sorry
```
#### Proof sketch
1. `tendsto_matrixCoeff_column`: `tendsto_cofinite (u (single j 1))` (definitional unfolding of `matrixCoeff`).
2. `norm_matrixCoeff_le`: `(norm_apply_le _ i).trans (by simpa [norm_single, norm_one] using le_opNorm u (single j 1))`.
3. `ext_matrixCoeff`: `ext_single fun j ↦ ZeroAtInftyContinuousMap.ext fun i ↦ h i j`.
4. `hasSum_matrixCoeff_mul`: `have h := (hasSum_smul_apply_single u f).mapL (evalCLM R i)`; `simpa only [evalCLM_apply, smul_apply, smul_eq_mul, mul_comm] using h`.

#### Mathlib lemmas needed
`tendsto_cofinite`, `norm_apply_le`, `ContinuousLinearMap.Ultra.le_opNorm` [L1], `ext_single`, `hasSum_smul_apply_single` (T006), `HasSum.mapL`, `evalCLM_apply`, `smul_apply`, `mul_comm`.
#### Sources
[RM] convention 7 and §2.6.1 ("each column tends to `0` cofinitely, `‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`, and `(u f) i = ∑' j, matrixCoeff u i j * f j`"); [Buz07] l. 286–296 ("For all `i`, `lim_{j→∞} a_{i,j} = 0` … `|a_{i,j}| ≤ C` … In fact `C` can be taken to be `|φ|`"); [Bel] l. 2029–2034.
#### Generality decision
L38.1–L38.3 over any normed ring (L38.2 Tate); L38.4 commutative (decision 6).

### [T039] The norm is the supremum of the entries; `ofMatrix`
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: T038 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L39.1–L39.5

#### Statement
```lean
theorem opNorm_eq_iSup_matrixCoeff [NormOneClass R] [IsUltrametricDist R] [IsTate R]
    (u : C₀(J, R) →L[R] C₀(I, R)) : ‖u‖ = ⨆ p : I × J, ‖matrixCoeff u p.1 p.2‖ := by
  sorry

noncomputable def ofMatrix (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) : C₀(J, R) →L[R] C₀(I, R) :=
  ofBounded R (fun j ↦ ofTendsto (fun i ↦ a i j) (hcol j)) (by sorry)

@[simp]
theorem matrixCoeff_ofMatrix (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) (i : I) (j : J) : matrixCoeff (ofMatrix a hcol hbdd) i j = a i j := by
  sorry

theorem ofMatrix_apply (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) (f : C₀(J, R)) (i : I) :
    ofMatrix a hcol hbdd f i = ∑' j, a i j * f j := by
  sorry

theorem norm_ofMatrix [NormOneClass R] [IsTate R] (a : I → J → R)
    (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) :
    ‖ofMatrix a hcol hbdd‖ = ⨆ p : I × J, ‖a p.1 p.2‖ := by
  sorry
```
#### Proof sketch
1. `opNorm_eq_iSup_matrixCoeff`: `le_antisymm`: (≤) `opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun f ↦ norm_le_of_forall_le (mul_nonneg …) fun i ↦ ?_`;
   `(u f) i = ∑' j, matrixCoeff u i j * f j` (`(hasSum_matrixCoeff_mul u f i).tsum_eq`), bounded by `IsUltrametricDist.norm_tsum_le_of_forall_le` with each term
   `‖a i j * f j‖ ≤ ‖a i j‖ * ‖f j‖ ≤ (⨆ p, ‖a p.1 p.2‖) * ‖f‖` (`norm_mul_le`, `le_ciSup ⟨‖u‖, …⟩ (i, j)` using `norm_matrixCoeff_le`, `norm_apply_le`);
   (≥) `Real.iSup_le (fun p ↦ norm_matrixCoeff_le u p.1 p.2) (opNorm_nonneg _)`.
2. `ofMatrix`'s bound: `obtain ⟨C, hC⟩ := hbdd; exact ⟨max C 0, fun j ↦ norm_le_of_forall_le (le_max_right _ _) fun i ↦ (hC i j).trans (le_max_left _ _)⟩`.
3. `matrixCoeff_ofMatrix`: `show (ofBounded R _ _ (single j 1)) i = a i j; rw [ofBounded_single]; rfl`.
4. `ofMatrix_apply`: `rw [ofMatrix, ofBounded_apply, ← (summable_smul_of_bounded f _ _).hasSum.mapL (evalCLM R i) |>.tsum_eq]`-style: evaluate the tsum
   coordinatewise with `ContinuousLinearMap.map_tsum (evalCLM R i)` and `smul_apply`, `smul_eq_mul`, `mul_comm`.
5. `norm_ofMatrix`: `rw [opNorm_eq_iSup_matrixCoeff]; simp only [matrixCoeff_ofMatrix]`.

#### Mathlib lemmas needed
`ContinuousLinearMap.Ultra.{opNorm_le_bound, opNorm_nonneg}` [L1], `IsUltrametricDist.norm_tsum_le_of_forall_le`, `norm_mul_le`, `le_ciSup`, `Real.iSup_le`, `Real.iSup_nonneg`, `ofBounded_single`, `ofBounded_apply`, `summable_smul_of_bounded`, `ContinuousLinearMap.map_tsum`, `HasSum.tsum_eq`.
#### Sources
[RM] §2.6.1 ("Conversely a matrix `a : I → J → R` whose columns tend to `0` cofinitely and whose entries are bounded is the matrix of a unique bounded operator, of norm `sup ‖a i j‖`"); [Buz07] l. 297–300 ("there is a unique continuous `φ : M → N` with norm `sup_{i,j} |a_{i,j}|` whose associated matrix is `(a_{i,j})`"); [Bel] l. 2031–2034.
#### Generality decision
`[IsUltrametricDist R] [CompleteSpace R]` for `ofMatrix` (the target `C₀(I, R)` must be ultrametric and complete for `ofBounded`); `[NormOneClass R] [IsTate R]` for the norm formulas.

### [T040] The matrix of a composite is the matrix product
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: T039 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L40.1–L40.2

#### Statement
```lean
theorem summable_matrixCoeff_mul_matrixCoeff [NormOneClass R] [IsTate R]
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(L, R) →L[R] C₀(J, R)) (i : I) (l : L) :
    Summable fun j ↦ matrixCoeff u i j * matrixCoeff v j l := by
  sorry

theorem matrixCoeff_comp [NormOneClass R] [IsTate R] (u : C₀(J, R) →L[R] C₀(I, R))
    (v : C₀(L, R) →L[R] C₀(J, R)) (i : I) (l : L) :
    matrixCoeff (u.comp v) i l = ∑' j, matrixCoeff u i j * matrixCoeff v j l := by
  sorry
```
#### Proof sketch
1. `summable_matrixCoeff_mul_matrixCoeff`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; the family tends to `0` by `squeeze_zero_norm`
   with `‖a i j * b j l‖ ≤ ‖u‖ * ‖b j l‖` (`norm_mul_le`, `norm_matrixCoeff_le`) and `((tendsto_matrixCoeff_column v l).norm.const_mul _)`.
2. `matrixCoeff_comp`: `unfold matrixCoeff; rw [comp_apply]`; `(u (v (single l 1))) i = ∑' j, matrixCoeff u i j * (v (single l 1)) j` is
   `(hasSum_matrixCoeff_mul u (v (single l 1)) i).tsum_eq.symm`, and `(v (single l 1)) j = matrixCoeff v j l` by definition.

#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `squeeze_zero_norm`, `norm_mul_le`, `Filter.Tendsto.const_mul`, `ContinuousLinearMap.comp_apply`, `HasSum.tsum_eq`.
#### Sources
[RM] §2.6.1 ("The matrix of a composite is the matrix product, with the middle sum convergent by §0.1.4"); [Buz07] l. 300–303 ("if `φ` and `ψ` … the matrix of `ψ ∘ φ` is the product"); [L0] `Sums.lean` (`tendsto_cofinite_prod_of_norm_le_mul`, the bounded-times-null principle).
#### Generality decision
Commutative scalars (decision 6); `[IsTate R]` for the boundedness of `u`'s entries.

### [CLEANUP-17] Run `/cleanup` on `ModelSpace/Matrix.lean`
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: T038, T039, T040 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Matrix.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T041] Diagonal and permutation operators
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: CLEANUP-17 · **Parallel**: no · **Type**: definitions + lemmas
- **Leaves**: L41.1–L41.7

#### Statement
```lean
noncomputable def diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) :
    C₀(I, R) →L[R] C₀(I, R) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ d i * f i) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    C (by sorry)

theorem matrixCoeff_diagonal [DecidableEq I] (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) (i j : I) :
    matrixCoeff (diagonal d C hd) i j = if i = j then d i else 0 := by
  sorry

theorem norm_diagonal [NormOneClass R] [IsTate R] [DecidableEq I] (d : I → R) (C : ℝ)
    (hd : ∀ i, ‖d i‖ ≤ C) : ‖diagonal d C hd‖ = ⨆ i, ‖d i‖ := by
  sorry

theorem injective_diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C)
    (h : ∀ i, ∀ x : R, d i * x = 0 → x = 0) : Injective (diagonal d C hd) := by
  sorry

theorem denseRange_diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) (h : ∀ i, IsUnit (d i)) :
    DenseRange (diagonal d C hd) := by
  sorry

noncomputable def diagonalEquiv (d : I → Rˣ) (hd : ∀ i, IsMultiplicative (d i : R))
    (h1 : ∀ i, ‖(d i : R)‖ = 1) : C₀(I, R) ≃ₗᵢ[R] C₀(I, R) where
  toFun f := ofTendsto (fun i ↦ (d i : R) * f i) (by sorry)
  invFun f := ofTendsto (fun i ↦ ((d i)⁻¹ : Rˣ) * f i) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

theorem matrixCoeff_reindex [DecidableEq I] (σ : I ≃ I) (i j : I) :
    matrixCoeff (reindex (R := R) (E := R) σ).toContinuousLinearEquiv.toContinuousLinearMap i j =
      if i = σ j then 1 else 0 := by
  sorry
```
#### Proof sketch
1. `diagonal`: tendsto by `squeeze_zero_norm` with `‖d i * f i‖ ≤ max C 0 * ‖f i‖`; `map_add'`: `mul_add`; `map_smul'`: `mul_left_comm`; the `mkContinuous` bound:
   `rcases isEmpty_or_nonempty I` — empty: `f = 0` and both sides vanish; nonempty: `0 ≤ C` (from `hd i`), then `norm_le_of_forall_le (mul_nonneg hC (norm_nonneg f))`
   with `norm_mul_le`, `hd i`, `norm_apply_le`.
2. `matrixCoeff_diagonal`: `by_cases h : i = j <;> simp [matrixCoeff, diagonal_apply, coe_single, Pi.single_apply, h]`.
3. `norm_diagonal`: `le_antisymm (opNorm_le_bound _ (Real.iSup_nonneg …) fun f ↦ norm_le_of_forall_le … fun i ↦ (norm_mul_le _ _).trans (mul_le_mul (le_ciSup ⟨C, …⟩ i) (norm_apply_le f i) …))`
   and `Real.iSup_le (fun i ↦ by simpa [norm_single, norm_one, diagonal_apply, single_apply_self] using le_opNorm_of_bound (diagonal d C hd) ⟨_, …⟩ (single i 1)) (opNorm_nonneg _)`
   (the value at `single i 1` has coordinate `d i` at `i`, so `‖d i‖ ≤ ‖diagonal d C hd (single i 1)‖`).
4. `injective_diagonal`: `fun f g hfg ↦ ext fun i ↦ h i _ (by have := congrArg (· i) hfg; rw [diagonal_apply, diagonal_apply] at this; rw [mul_sub, this, sub_self])`
   (then `sub_eq_zero`).
5. `denseRange_diagonal`: `DenseRange` is `Dense (Set.range _)`; `Dense.mono (Submodule.span_le.2 ?_) dense_span_range_single_one` where
   `single i 1 = diagonal d C hd (single i ((h i).unit⁻¹ : R))` (`ext j`, `by_cases j = i`, `Units.mul_inv`).
6. `diagonalEquiv`: tendsto from `‖d i * f i‖ = ‖f i‖` (`(hd i).norm_mul`, `h1 i`, `one_mul`); inverse `((d i)⁻¹ : Rˣ)` is multiplicative of norm `1`
   (`IsMultiplicative.inv`, `IsMultiplicative.norm_inv`); `map_add'`/`map_smul'`: `mul_add`, `mul_left_comm`; inverses: `Units.inv_mul_cancel_left`,
   `Units.mul_inv_cancel_left`; `norm_map'`: sandwich with `‖d i * f i‖ = ‖f i‖`.
7. `matrixCoeff_reindex`: `simp [matrixCoeff, reindex_apply, coe_single, Pi.single_apply, Equiv.symm_apply_eq]`.

#### Mathlib lemmas needed
`squeeze_zero_norm`, `mul_add`, `mul_left_comm`, `isEmpty_or_nonempty`, `norm_mul_le`, `le_ciSup`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound, opNorm_nonneg}` [L1], `Pi.single_apply`, `mul_sub`, `sub_eq_zero`, `Dense.mono`, `Submodule.span_le`, `IsUnit.unit`, `Units.mul_inv`, `NormedRing.IsMultiplicative.{norm_mul, inv, norm_inv}` [L0], `Units.inv_mul_cancel_left`, `Equiv.symm_apply_eq`.
#### Sources
[RM] §2.6.2 ("The diagonal operator of a bounded family `d : I → R` has norm `sup ‖dᵢ‖`; it is an isometric automorphism when every `dᵢ` is a multiplicative unit of norm `1`, and injective with dense range when every `dᵢ` is a non-zero-divisor [E22: unit for dense range] … The permutation operator of `σ : I ≃ I` is an isometric automorphism"); Layer 1 Examples ("diagonal operator").
#### Generality decision
Commutative `R`; `norm_diagonal` is proved without ultrametricity; E22 for `denseRange_diagonal`.

### [T042] Base change of matrices along a bounded ring homomorphism (Johansson–Newton 2.1.8)
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: T041, CLEANUP-6 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L42.1–L42.5

#### Statement
```lean
noncomputable def baseChange (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (u : C₀(J, R) →L[R] C₀(I, R)) :
    C₀(J, S) →L[S] C₀(I, S) :=
  ofMatrix (fun i j ↦ φ (matrixCoeff u i j)) (by sorry) (by sorry)

@[simp]
theorem matrixCoeff_baseChange (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    matrixCoeff (baseChange φ C hφ u) i j = φ (matrixCoeff u i j) := by
  sorry

theorem baseChange_map (u : C₀(J, R) →L[R] C₀(I, R)) (f : C₀(J, R)) :
    baseChange φ C hφ u (map φ C hφ f) = map φ C hφ (u f) := by
  sorry

theorem norm_baseChange_le [NormOneClass S] [IsTate S] (hC : 0 ≤ C)
    (u : C₀(J, R) →L[R] C₀(I, R)) : ‖baseChange φ C hφ u‖ ≤ C * ‖u‖ := by
  sorry

theorem baseChange_symm_baseChange [IsUltrametricDist R] [CompleteSpace R] [NormOneClass S]
    [IsTate S] (e : R ≃+* S) (C' : ℝ) (he : ∀ r, ‖e r‖ ≤ C * ‖r‖) (he' : ∀ s, ‖e.symm s‖ ≤ C' * ‖s‖)
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    baseChange e.symm.toRingHom C' he' (baseChange e.toRingHom C he u) = u := by
  sorry
```
#### Proof sketch
1. `baseChange`'s two obligations: columns tend to `0` by `squeeze_zero_norm` with `‖φ (a i j)‖ ≤ max C 0 * ‖a i j‖` and `tendsto_matrixCoeff_column`;
   entries bounded by `max C 0 * ‖u‖` (`norm_matrixCoeff_le`).
2. `matrixCoeff_baseChange`: `matrixCoeff_ofMatrix _ _ _ i j`.
3. `baseChange_map`: `ext i`; LHS `= ∑' j, φ (a i j) * φ (f j)` (`ofMatrix_apply`, `map_apply`); RHS `= φ (∑' j, a i j * f j)` (`map_apply`, `(hasSum_matrixCoeff_mul u f i).tsum_eq`);
   `φ` is continuous (`AddMonoidHomClass.continuous_of_bound φ C hφ`), so `((hasSum_matrixCoeff_mul u f i).map φ hcont)` with `map_mul` gives the equality via `HasSum.tsum_eq`.
4. `norm_baseChange_le`: `rw [norm_ofMatrix]; exact Real.iSup_le (fun p ↦ (hφ _).trans (mul_le_mul_of_nonneg_left (norm_matrixCoeff_le u _ _) hC)) (mul_nonneg hC (opNorm_nonneg u))`.
5. `baseChange_symm_baseChange`: `ext_matrixCoeff fun i j ↦ by simp only [matrixCoeff_baseChange, RingEquiv.symm_toRingHom_apply? , RingEquiv.symm_apply_apply]`.

#### Mathlib lemmas needed
`squeeze_zero_norm`, `tendsto_matrixCoeff_column`, `norm_matrixCoeff_le` (T038), `matrixCoeff_ofMatrix`, `ofMatrix_apply`, `norm_ofMatrix` (T039), `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `map_mul`, `Real.iSup_le`, `RingEquiv.symm_apply_apply`, `ext_matrixCoeff`.
#### Sources
[RM] §2.6.6 ("For a bounded ring homomorphism `φ : R → S`, the operator `C₀(J, S) → C₀(I, S)` with matrix `φ (matrixCoeff u i j)` exists, is `φ`-semilinearly compatible with `u`, and has norm at most `‖φ‖ ‖u‖`; a bicontinuous ring isomorphism transports bounded operators (Johansson–Newton, Proposition 2.1.8, the part that does not mention compactness)"); [JN] l. 655–660 ("If we change the norms on `(R, M)` to equivalent ones, then `M` still has property (Pr)").
#### Generality decision
`R` Tate (bounded entries), `S` ultrametric complete (for `ofMatrix`), both `NormOneClass`/Tate for the norm bound.

### [CLEANUP-18] Run `/cleanup` on `ModelSpace/Matrix.lean`
- **Status**: open · **File**: `ModelSpace/Matrix.lean` · **Depends on**: T041, T042 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Matrix.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T043] The dual of the model space is `ℓ^∞`
- **Status**: open · **File**: `ModelSpace/Dual.lean` · **Depends on**: CLEANUP-17 · **Parallel**: no · **Type**: definition + lemmas
- **Leaves**: L43.1–L43.3

#### Statement
```lean
theorem memℓp_infty_apply_single [NormOneClass R] [IsTate R] (l : C₀(I, R) →L[R] R) :
    Memℓp (fun i ↦ l (single i 1)) ∞ := by
  sorry

noncomputable def dualEquivLp [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R] :
    (C₀(I, R) →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞ where
  toFun l := ⟨fun i ↦ l (single i 1), memℓp_infty_apply_single l⟩
  invFun l := ofBounded R (fun i ↦ l i) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

theorem dualEquivLp_symm_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    (l : lp (fun _ : I ↦ R) ∞) (f : C₀(I, R)) :
    (dualEquivLp R I).symm l f = ∑' i, f i * l i := by
  sorry
```
#### Proof sketch
1. `memℓp_infty_apply_single`: `obtain ⟨C, hC⟩ := exists_bound_single l; exact memℓp_infty ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩`.
2. `dualEquivLp`: `invFun`'s bound `⟨‖l‖, fun i ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero l i⟩`; `map_add'`: `lp.ext (funext fun i ↦ by simp [add_apply])`;
   `map_smul'`: `lp.ext (funext fun i ↦ by simp [ContinuousLinearMap.smul_apply, smul_eq_mul, lp.coeFn_smul])`; `left_inv l := (eq_ofBounded l).symm`;
   `right_inv l := lp.ext (funext fun i ↦ ofBounded_single _ _ i)`; `norm_map' l`: `‖(l (single i 1))ᵢ‖ = ⨆ i, ‖l (single i 1)‖` (`lp.norm_eq_ciSup`)
   `= ‖ofBounded R (fun i ↦ l (single i 1)) _‖` (`norm_ofBounded`) `= ‖l‖` (`eq_ofBounded`).
3. `dualEquivLp_symm_apply`: `show ofBounded R _ _ f = _; rw [ofBounded_apply]; rfl` (`f i • l i = f i * l i`, `smul_eq_mul`).

#### Mathlib lemmas needed
`memℓp_infty`, `lp.norm_apply_le_norm`, `ENNReal.top_ne_zero`, `lp.ext`, `lp.coeFn_smul`, `lp.norm_eq_ciSup`, `exists_bound_single`, `eq_ofBounded`, `ofBounded_single`, `norm_ofBounded` (T006–T008).
#### Sources
[RM] §2.5.1 ("the continuous dual of `C₀(I, R)` is `ℓ^∞(I, R)` (bounded families, sup norm) isometrically, by the universal property §2.1.3: a functional is determined by its values on the coordinate vectors, and `‖λ‖ = sup ‖λ (single i 1)‖`"); [Sch] §3 Example l. 617–700 ("`c₀(X)' = ℓ^∞(X)`"); [Col] §3 l. 172–176.
#### Generality decision
`R` commutative (Layer 1's module structure on the dual), Banach–Tate, ultrametric, `NormOneClass`; the scoped operator norm (decision 9).

### [T044] The pairing with `ℓ^∞` and the evaluation into the bidual
- **Status**: open · **File**: `ModelSpace/Dual.lean` · **Depends on**: T043 · **Parallel**: no · **Type**: lemmas + definition
- **Leaves**: L44.1–L44.4

#### Statement
```lean
theorem summable_lp_mul [IsUltrametricDist R] [CompleteSpace R] (l : lp (fun _ : I ↦ R) ∞)
    (f : C₀(I, R)) : Summable fun i ↦ l i * f i := by
  sorry

theorem norm_tsum_lp_mul_le [IsUltrametricDist R] [CompleteSpace R] (l : lp (fun _ : I ↦ R) ∞)
    (f : C₀(I, R)) :
    ‖∑' i, l i * f i‖ ≤ ‖l‖ * ‖f‖ := by
  sorry

theorem continuous_pairing [IsUltrametricDist R] [CompleteSpace R] :
    Continuous fun p : lp (fun _ : I ↦ R) ∞ × C₀(I, R) ↦ ∑' i, p.1 i * p.2 i := by
  sorry

noncomputable def toBidual [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R] :
    C₀(I, R) →ₗᵢ[R] (lp (fun _ : I ↦ R) ∞ →L[R] R) where
  toFun f :=
    LinearMap.mkContinuous
      { toFun := fun l ↦ ∑' i, l i * f i
        map_add' := by sorry
        map_smul' := by sorry }
      ‖f‖ (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  norm_map' := by sorry
```
#### Proof sketch
1. `summable_lp_mul`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; `squeeze_zero_norm` with `‖l i * f i‖ ≤ ‖l‖ * ‖f i‖` (`norm_mul_le`,
   `lp.norm_apply_le_norm`) and `(tendsto_cofinite f).norm.const_mul _`.
2. `norm_tsum_lp_mul_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le (mul_nonneg (norm_nonneg l) (norm_nonneg f)) fun i ↦ (norm_mul_le _ _).trans (mul_le_mul (lp.norm_apply_le_norm _ l i) (norm_apply_le f i) (norm_nonneg _) (norm_nonneg _))`.
3. `continuous_pairing`: `continuous_iff_continuousAt.2 fun ⟨l₀, f₀⟩ ↦ Metric.continuousAt_iff.2 fun ε hε ↦ ?_`; write
   `⟨l, f⟩ - ⟨l₀, f₀⟩ = ⟨l - l₀, f⟩ + ⟨l₀, f - f₀⟩` (`tsum_sub`, `tsum_add` of summable families, `sub_mul`, `mul_sub`), bound each by step 2, and use the ultrametric
   inequality; choose `δ := min 1 (ε / (2 * (‖l₀‖ + ‖f₀‖ + 1)))`-type constant (`Prod.dist_eq`, `max_lt_iff`).
4. `toBidual`: inner `map_add'`: `(summable_lp_mul l f).tsum_add (summable_lp_mul l' f)` after `lp.coeFn_add`, `add_mul`; inner `map_smul'`:
   `lp.coeFn_smul`, `smul_eq_mul`, `mul_assoc`, `(summable_lp_mul l f).tsum_const_smul`-type (`tsum_mul_left`); inner bound: `norm_tsum_lp_mul_le` with `mul_comm`;
   outer `map_add'`/`map_smul'`: `ContinuousLinearMap.ext fun l ↦ ?_` with `mul_add`/`mul_left_comm` and `tsum_add`/`tsum_mul_right`;
   `norm_map'`: `le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun l ↦ by rw [mul_comm]; exact norm_tsum_lp_mul_le l f)` and, for `≥`,
   `Real.iSup_le`/`norm_eq_iSup` with `‖f i‖ = ‖toBidual f (lp.single ∞ i 1)‖` (`lp.single_apply`, `tsum_eq_single i`, `one_mul`) `≤ ‖toBidual f‖ * ‖lp.single ∞ i 1‖`
   (`le_opNorm_of_bound`) and `‖lp.single ∞ i 1‖ = 1` (`lp.norm_eq_ciSup`, `lp.single_apply`, `norm_one`, `[NormOneClass R]`).

#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `squeeze_zero_norm`, `norm_mul_le`, `lp.norm_apply_le_norm`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `continuous_iff_continuousAt`, `Metric.continuousAt_iff`, `Prod.dist_eq`, `tsum_add`, `tsum_sub`, `tsum_mul_left`, `tsum_mul_right`, `lp.coeFn_add`, `lp.coeFn_smul`, `lp.single`, `lp.single_apply`, `tsum_eq_single`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound}` [L1].
#### Sources
[RM] §2.5.2 ("The pairing `ℓ^∞(I, R) × C₀(I, R) → R`, `⟨λ, f⟩ = ∑' λᵢ fᵢ`, is continuous with `‖⟨λ, f⟩‖ ≤ ‖λ‖ ‖f‖`, and the evaluation `C₀ → (C₀)'' = (ℓ^∞)'` is an isometric embedding. ⚠ It is not surjective"); [Sch] §3 l. 617–700.
#### Generality decision
`toBidual` needs `[IsTate R]` only because the operator-norm instance on `lp … →L[R] R` does; non-surjectivity (non-reflexivity) is out of scope, as the roadmap says.

### [T045] Transposes and the dual of an orthonormalisable module
- **Status**: open · **File**: `ModelSpace/Dual.lean` · **Depends on**: T044, CLEANUP-12 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L45.1–L45.3

#### Statement
```lean
theorem dualEquivLp_comp_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    (u : C₀(J, R) →L[R] C₀(I, R)) (l : C₀(I, R) →L[R] R) (j : J) :
    dualEquivLp R J (l.comp u) j = ∑' i, dualEquivLp R I l i * matrixCoeff u i j := by
  sorry

theorem opNorm_comp_linearIsometryEquiv (u : N →L[R] P) (e : M ≃ₗᵢ[R] N) :
    ‖u.comp (e.toContinuousLinearEquiv : M →L[R] N)‖ = ‖u‖ := by
  sorry

theorem Module.IsONable.exists_dual_linearIsometryEquiv_lp {R : Type u} {M : Type v}
    [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R]
    [CompleteSpace R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] (h : IsONable R M) :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I),
      Nonempty ((M →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞) := by
  sorry
```
#### Proof sketch
1. `dualEquivLp_comp_apply`: LHS `= l (u (single j 1))` (`dualEquivLp_apply`, `comp_apply`); `u (single j 1) = ∑' i, matrixCoeff u i j • single i 1`
   (`hasSum_smul_single_one`), so `l (…) = ∑' i, matrixCoeff u i j * l (single i 1)` (`HasSum.mapL l`, `map_smul`, `smul_eq_mul`, `HasSum.tsum_eq`); finish with `mul_comm`.
2. `opNorm_comp_linearIsometryEquiv`: `le_antisymm (opNorm_le_bound _ (opNorm_nonneg u) fun x ↦ by rw [comp_apply, ← e.norm_map x]; exact le_opNorm u (e x))
   (opNorm_le_bound _ (opNorm_nonneg _) fun y ↦ by have := le_opNorm (u.comp _) (e.symm y); rwa [comp_apply, e.apply_symm_apply, e.symm.norm_map]? …)`
   — the second direction evaluates at `e.symm y` and uses `‖e.symm y‖ = ‖y‖`.
3. `exists_dual_linearIsometryEquiv_lp`: `obtain ⟨I, _, _, ⟨Φ⟩⟩ := h; classical`; the precomposition `(M →L[R] R) ≃ₗᵢ[R] (C₀(I, R) →L[R] R)`:
   `LinearIsometryEquiv.mk` on the `LinearEquiv` with `toFun l := l.comp Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap`, inverse with `Φ`,
   `map_add'`/`map_smul'` by `ext; rfl`, inverses by `ext; simp`, and `norm_map'` from step 2; then `⟨I, _, _, ⟨(this).trans (dualEquivLp R I)⟩⟩`.

#### Mathlib lemmas needed
`hasSum_smul_single_one` (T005), `HasSum.mapL`, `HasSum.tsum_eq`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm, opNorm_nonneg}` [L1], `LinearIsometryEquiv.{norm_map, apply_symm_apply}`, `LinearIsometryEquiv.mk`, `LinearIsometryEquiv.trans`.
#### Sources
[RM] §2.5.3 ("For an orthonormalisable `M` with basis `e`, the dual is identified with bounded families indexed by the basis, and the transpose of `u : M →L[R] N` between orthonormalisable modules has the transposed matrix (§2.6)"); [Buz07] l. 284–296 (the matrix entries are the coordinates of the images of the basis).
#### Generality decision
The transpose is precomposition `l ↦ l.comp u` (no separate definition); `opNorm_comp_linearIsometryEquiv` is a Layer-1-style helper placed here because nothing in Layer 1 needs it.

### [CLEANUP-19] Run `/cleanup` on `ModelSpace/Dual.lean`
- **Status**: open · **File**: `ModelSpace/Dual.lean` · **Depends on**: T043, T044, T045 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Dual.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T046] Approximation of finitely generated closed submodules (Bellaïche 3.1.12)
- **Status**: open · **File**: `ModelSpace/Closed.lean` · **Depends on**: CLEANUP-7, CLEANUP-17 · **Parallel**: yes (parallel with the Dual chain) · **Type**: lemma
- **Leaves**: L46.1

#### Statement
```lean
theorem exists_truncation_near (P : Submodule R C₀(I, R)) (hP : P.FG)
    (hclosed : IsClosed (P : Set C₀(I, R))) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ p ∈ P, ‖truncation (↑S : Set I) p - p‖ ≤ ε * ‖p‖ := by
  sorry
```
#### Proof sketch
`obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hP` (`Submodule.span R (Set.range g) = P`);
`obtain ⟨C, hC0, hC⟩ := NormedRing.exists_forall_exists_eq_sum_smul_norm_le g P hclosed hg` (Layer 1: every `p ∈ P` is `∑ k, a k • g k` with `‖a k‖ ≤ C * ‖p‖`);
for each `k`, `tendsto_truncation_finset (g k)` and `Metric.tendsto_atTop` give `s k : Finset I` with `‖truncation ↑(s k) (g k) - g k‖ ≤ ε / C` for all larger finsets;
`S := Finset.univ.sup s`; by monotonicity (`norm_sub_truncation_le` with `s k ⊆ S`) the same holds for `S`. For `p ∈ P` write `p = ∑ k, a k • g k`;
`truncation ↑S p - p = ∑ k, a k • (truncation ↑S (g k) - g k)` (`map_sum`, `map_smul`, `Finset.sum_sub_distrib`, `smul_sub`), so
`‖truncation ↑S p - p‖ ≤ max_k ‖a k‖ * ‖…‖ ≤ (C * ‖p‖) * (ε / C) = ε * ‖p‖` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `mul_div_cancel₀`).

#### Mathlib lemmas needed
`Submodule.fg_iff_exists_fin_generating_family`, `NormedRing.exists_forall_exists_eq_sum_smul_norm_le` [L1], `tendsto_truncation_finset` (T016), `Metric.tendsto_atTop`, `Finset.sup`, `Finset.le_sup`, `norm_sub_truncation_le` (T014), `map_sum`, `map_smul`, `Finset.sum_sub_distrib`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `mul_div_cancel₀`.
#### Sources
[Bel] Lemma II.1.8 l. 2043–2056 ("Since `P` is finite, there exists a surjective continuous morphism `π : A^r → P`. By the open mapping theorem, there is a constant `c > 0` such that for every `p ∈ P`, there exists `m ∈ A^r` such that `π(m) = p` and `|m| ≤ c|p|` … there exists a finite subset `S` of `I` such that `|π_S(π(e_i)) − π(e_i)| ≤ ε/c` … `|π_S(p) − p| ≤ ε|m|/c ≤ ε|p|`"); [Buz07] Lemma 2.3(c) l. 370–390; [RM] §2.6.4 ("The proof is the open mapping theorem applied to a surjection `R ^ r → P`, which is why closedness is a hypothesis").
#### Generality decision
Closedness is a hypothesis (the counterexample is T055); `R` commutative Banach–Tate ultrametric (Layer 1's OMT corollary).

### [CLEANUP-ALL-4] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: T046, CLEANUP-18 · **Parallel**: no · **Type**: cleanup
- **Description**: Pre-milestone sweep before M4. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T047] MILESTONE M4 — finitely generated submodules of the model space are closed over a Noetherian ring (Buzzard 2.3)
- **Status**: open · **File**: `ModelSpace/Closed.lean` · **Depends on**: CLEANUP-ALL-4 · **Parallel**: no · **Type**: milestone
- **Leaves**: L47.1–L47.2

#### Statement
```lean
theorem exists_truncation_injOn (P : Submodule R C₀(I, R)) (hP : P.FG) :
    ∃ S : Finset I, Set.InjOn (truncation (R := R) (↑S : Set I)) (P : Set C₀(I, R)) := by
  sorry

theorem isClosed_of_fg (P : Submodule R C₀(I, R)) (hP : P.FG) : IsClosed (P : Set C₀(I, R)) := by
  sorry
```
#### Proof sketch
1. `exists_truncation_injOn`: generators `g : Fin n → C₀(I, R)` of `P`; column vectors `c : I → (Fin n → R)`, `c i k := g k i`; `N := Submodule.span R (Set.range c)`
   is finitely generated (`IsNoetherian.noetherian N`, `Fin n → R` is a Noetherian module over the Noetherian `R`); from `N.FG` and
   `Submodule.mem_span_finite_of_mem_span` (each generator of `N` lies in the span of finitely many `c i`) extract a finite `S : Finset I` with `N = span (c '' S)`
   (`Finset.biUnion`, `Submodule.span_le`, `Submodule.span_mono`). Injectivity on `P`: for `p = ∑ a k • g k`, `q = ∑ b k • g k`
   (`Submodule.mem_span_range_iff_exists_fun`) with `truncation ↑S p = truncation ↑S q`, the linear functional `λ v := ∑ k, (a k - b k) * v k` on `Fin n → R`
   vanishes on `c i` for `i ∈ S` (coordinates of `truncation ↑S (p - q)`), hence on `N` (`Submodule.span_le` into `LinearMap.ker λ`), hence on every `c i`,
   i.e. `(p - q) i = 0` for all `i` (`sum_apply`, `smul_apply`); so `p = q`.
2. `isClosed_of_fg`: with `S` from 1, let `F := LinearMap.range (truncation (R := R) ↑S)` (finite free: `range_truncation_finset`, `Module.Finite.span_of_finite`),
   `Q := P.map (truncation ↑S) ≤ F`; `Q` is closed in `F` by Layer 1's `Submodule.isClosed_of_isNoetherianRing` (on the Banach module `F`, closed in `C₀`), hence closed in
   `C₀(I, R)` and complete; `τ : P →L[R] Q` is a continuous linear bijection (injective by 1, surjective by construction) and its algebraic inverse `ψ : Q →ₗ[R] P`
   is continuous by Layer 1's `continuous_of_finite` (`Q` is finitely generated: a submodule of the Noetherian module `F`; `Q` complete, ultrametric);
   so `P ≃L[R] Q` and `P` is complete (`UniformEquiv.completeSpace_iff` after `AddMonoidHomClass.uniformContinuous_of_continuousAt_zero` both ways), hence closed
   (`completeSpace_coe_iff_isComplete`, `IsComplete.isClosed`). Pattern: [SRC] `05_Noetherian.lean` `isClosed_of_fg`.

#### Mathlib lemmas needed
`IsNoetherian.noetherian`, `Submodule.mem_span_finite_of_mem_span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_le`, `LinearMap.ker`, `range_truncation_finset` (T015), `Module.Finite.span_of_finite`, `Submodule.isClosed_of_isNoetherianRing` [L1], `ContinuousLinearMap.Ultra.continuous_of_finite` [L1], `AddMonoidHomClass.uniformContinuous_of_continuousAt_zero`, `UniformEquiv.completeSpace_iff`, `completeSpace_coe_iff_isComplete`, `IsComplete.isClosed`.
#### Sources
[Buz07] Lemma 2.3(a)–(b) l. 335–369 ("For `i ∈ I` let `v_i` be the element `(a_{α,i})` of `A^r`. The `A`-submodule of `A^r` generated by the `v_i` is finitely-generated, as `A` is Noetherian, and hence there is a finite set `S ⊆ I` such that this module is generated by `{v_i : i ∈ S}` … (b) … the injection `P → A^S` induces a continuous injection from `P` onto a submodule of `A^S` which is closed by Proposition 3.7.3/1 of [1] … continuous by Lemma 2.2 … and hence the norms on `P` and `Q` are equivalent"); [Lud] Lemma 2.26 l. 371–395; [RM] §2.6.5 ("This discharges the hypothesis of clause 4 over Noetherian bases and is the statement §1.4.3 defers to here").
#### Generality decision
`[IsNoetherianRing R]` with `R` commutative Banach–Tate ultrametric; the Noetherian hypothesis is used exactly twice (the column module, the closedness in `F`).

### [CLEANUP-20] Run `/cleanup` on `ModelSpace/Closed.lean`
- **Status**: open · **File**: `ModelSpace/Closed.lean` · **Depends on**: T047 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Closed.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T048] Surjectivity by successive approximation; the columns of a unitriangular perturbation
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: CLEANUP-17, CLEANUP-12 · **Parallel**: yes (parallel with Dual/Closed) · **Type**: lemmas
- **Leaves**: L48.1–L48.2

#### Statement
```lean
theorem surjective_of_forall_exists_approx (u : M →L[R] N) {q C : ℝ} (hq : q < 1)
    (h : ∀ y, ∃ x, ‖x‖ ≤ C * ‖y‖ ∧ ‖y - u x‖ ≤ q * ‖y‖) : Surjective u := by
  sorry

theorem tendsto_column (j : ℕ) : Tendsto (fun i ↦ a i j) cofinite (𝓝 0) := by
  sorry
```
#### Proof sketch
1. `surjective_of_forall_exists_approx`: `intro y; choose g hg₁ hg₂ using h`; `q' := max q 0` (`q' < 1`, `0 ≤ q'`); `r n := (fun z ↦ z - u (g z))^[n] y`;
   `‖r n‖ ≤ q' ^ n * ‖y‖` by induction (`Function.iterate_succ_apply'`, `hg₂`, `mul_le_mul_of_nonneg_left`); `x := ∑' n, g (r n)` is summable
   (`Summable.of_norm_bounded _ (summable_geometric_of_lt_one … |>.mul_left (C * ‖y‖))`, `hg₁`); `u x = ∑' n, u (g (r n))` (`ContinuousLinearMap.map_tsum`)
   `= ∑' n, (r n - r (n + 1))` (`Function.iterate_succ_apply'`, `sub_sub_cancel`) `= y - lim r n = y` (`HasSum.tendsto_sum_nat`, `Finset.sum_range_sub'`,
   `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_nhds_unique`). Pattern: Layer 1 `OpenMapping.lean` l. 136–180.
2. `tendsto_column`: `tendsto_const_nhds.congr' (Filter.eventually_cofinite.2 (ha.column_finite j))`-style (`not_not`).

#### Mathlib lemmas needed
`Function.iterate_succ_apply'`, `Summable.of_norm_bounded`, `summable_geometric_of_lt_one`, `ContinuousLinearMap.map_tsum`, `HasSum.tendsto_sum_nat`, `Finset.sum_range_sub'`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_nhds_unique`, `Filter.eventually_cofinite`, `Filter.Tendsto.congr'`.
#### Sources
[RM] §2.7.1 ("`T` is surjective (successive approximation with contraction factor `q`)"); [L1] `exists_preimage_norm_le` (the same iteration with factor `1/2`).
#### Generality decision
The helper is stated over a Tate ring for `u` bounded (`le_opNorm`); `M` complete; no ultrametricity.

### [T049] A unitriangular perturbation is an isometry (the largest-index argument)
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: T048 · **Parallel**: no · **Type**: lemma
- **Leaves**: L49.1

#### Statement
```lean
theorem norm_toCLM_apply (f : C₀(ℕ, R)) : ‖ha.toCLM f‖ = ‖f‖ := by
  sorry
```
#### Proof sketch
`le_antisymm`: (≤) `norm_le_of_forall_le (norm_nonneg f) fun i ↦ ?_`: `ha.toCLM f i = ∑' j, a i j * f j` (`toCLM_apply`); `IsUltrametricDist.norm_tsum_le_of_forall_le
(norm_nonneg f) fun j ↦ (norm_mul_le _ _).trans (by simpa using mul_le_mul (ha.norm_le_one i j) (norm_apply_le f j) (norm_nonneg _) zero_le_one)`.
(≥) `by_cases hf : f = 0`; else `F := {j | ‖f j‖ = ‖f‖}` is nonempty (`exists_norm_apply_eq_norm`) and finite (`tendsto_cofinite f`: `‖f j‖ < ‖f‖` cofinitely,
`norm_pos_iff.2 hf`); `j₀ := F.toFinset.max' _`. Then `‖ha.toCLM f j₀‖ = ‖f‖` by Layer 0's `IsUltrametricDist.norm_tsum_eq_of_forall_lt` (summable: T039's
family; the term `j₀`: `‖a j₀ j₀ * f j₀‖ = ‖a j₀ j₀‖ * ‖f j₀‖ = ‖f‖` by `(ha.diag_isMultiplicative j₀).norm_mul` and `ha.norm_diag`; for `j ≠ j₀`:
if `j < j₀` then `‖a j₀ j * f j‖ ≤ q * ‖f j‖ ≤ q * ‖f‖ < ‖f‖` (`ha.norm_lower_le`, `ha.q_lt_one`; if `q ≤ 0` the bound is `≤ 0 < ‖f‖`);
if `j₀ < j` then `j ∉ F` (`Finset.le_max'`), so `‖f j‖ < ‖f‖` and `‖a j₀ j * f j‖ ≤ ‖f j‖ < ‖f‖` (`ha.norm_le_one`)); finally `‖f‖ = ‖ha.toCLM f j₀‖ ≤ ‖ha.toCLM f‖` (`norm_apply_le`).

#### Mathlib lemmas needed
`toCLM_apply`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `IsUltrametricDist.norm_tsum_eq_of_forall_lt` [L0], `exists_norm_apply_eq_norm` (T002), `Finset.max'`, `Finset.le_max'`, `norm_mul_le`, `NormedRing.IsMultiplicative.norm_mul` [L0], `norm_pos_iff`.
#### Sources
[RM] §2.7.1 ("`T` is an isometry (`‖T f‖ = ‖f‖`, by the largest-index argument: the largest index at which `‖fⱼ‖` is attained contributes a term that no other term can cancel)").
#### Generality decision
`R` commutative Banach ultrametric with `‖1‖ = 1`, no Tate hypothesis.

### [T050] Backward substitution and one step of the successive approximation
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: T049 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L50.1–L50.2

#### Statement
```lean
theorem exists_forall_tsum_eq_of_finite (g : C₀(ℕ, R)) (N : ℕ) (hg : ∀ i, N < i → g i = 0) :
    ∃ f : C₀(ℕ, R), ‖f‖ ≤ ‖g‖ ∧ (∀ i, N < i → f i = 0) ∧
      ∀ i, ∑' j, (if i ≤ j then a i j else 0) * f j = g i := by
  sorry

theorem exists_norm_sub_toCLM_le (g : C₀(ℕ, R)) :
    ∃ f : C₀(ℕ, R), ‖f‖ ≤ ‖g‖ ∧ ‖g - ha.toCLM f‖ ≤ max q 2⁻¹ * ‖g‖ := by
  sorry
```
#### Proof sketch
1. `exists_forall_tsum_eq_of_finite`: induction on `N`, the statement quantified over all `g` supported in `{i | i ≤ N}`. The sums are finite
   (`tsum_eq_sum` on `Finset.range (N + 1)` since `f j = 0` for `j > N`). **Base `N = 0`**: `f := single 0 ((ha.diag_isUnit 0).unit⁻¹ * g 0)`:
   row `0` gives `a 0 0 * ((a 0 0)⁻¹ * g 0) = g 0` (`Units.mul_inv_cancel_left`), rows `i > 0` give `0 = g i`; `‖f‖ = ‖g 0‖ ≤ ‖g‖` (`norm_single`,
   `(ha.diag_isMultiplicative 0).inv.norm_mul`, `ha.norm_diag`, `IsMultiplicative.norm_inv`). **Step `N → N + 1`**: `c := (ha.diag_isUnit (N+1)).unit⁻¹ * g (N+1)`,
   `g' := g - (fun i ↦ a i (N+1) * c)` truncated to `≤ N` (`ofTendsto`, `truncation (Set.Iic N)`): supported in `≤ N`, `‖g'‖ ≤ ‖g‖` (ultrametric, `‖a i (N+1) * c‖ ≤ ‖g (N+1)‖`);
   IH gives `f'`; `f := f' + single (N+1) c`; rows `i ≤ N`: `∑_{j ≥ i} a i j f j = (∑_{j ≥ i} a i j f' j) + a i (N+1) c = g' i + a i (N+1) c = g i`;
   row `N + 1`: `a (N+1) (N+1) * c = g (N+1)`; rows `> N + 1`: `0 = g i`; `‖f‖ ≤ max ‖f'‖ ‖c‖ ≤ ‖g‖` (`IsUltrametricDist.norm_add_le_max`).
2. `exists_norm_sub_toCLM_le`: `by_cases hg : g = 0` (take `f := 0`); else `q' := max q 2⁻¹`, `0 < q' < 1`; `tendsto_cofinite g` gives `N` with `‖g i‖ ≤ q' * ‖g‖`
   for `i > N` (`Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Finset.sup`); `g' := truncation (Set.Iic N) g`, `‖g - g'‖ ≤ q' * ‖g‖` (`norm_sub_truncation_le`);
   apply 1 to `g'` → `f` with `‖f‖ ≤ ‖g'‖ ≤ ‖g‖` and `(D + U) f = g'`; split `ha.toCLM f i = ∑' j, (if i ≤ j then a i j else 0) * f j + ∑' j, (if j < i then a i j else 0) * f j`
   (`tsum_add` of two summable families, each dominated by the summable `‖f j‖`-family; `ite` case split with `not_le`); the lower part has norm
   `≤ q * ‖f‖ ≤ q * ‖g‖` (`IsUltrametricDist.norm_tsum_le_of_forall_le`, `ha.norm_lower_le`; if `q < 0` it is `0`); hence
   `‖g - ha.toCLM f‖ = ‖(g - g') - L f‖ ≤ max (q' * ‖g‖) (q * ‖g‖) ≤ q' * ‖g‖` (`IsUltrametricDist.norm_sub_le_max`, `le_max_left`).

#### Mathlib lemmas needed
`tsum_eq_sum`, `Units.mul_inv_cancel_left`, `IsUnit.unit`, `NormedRing.IsMultiplicative.{inv, norm_inv, norm_mul}` [L0], `norm_single`, `single` (T004), `truncation`, `norm_sub_truncation_le` (T014), `IsUltrametricDist.{norm_add_le_max, norm_sub_le_max, norm_tsum_le_of_forall_le}`, `tsum_add`, `Summable.of_norm_bounded`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`.
#### Sources
[RM] §2.7.1 ("`T` is surjective (successive approximation with contraction factor `q`)"); the exact solution of the upper unitriangular part on a finite truncation is the roadmap's "finitely supported columns" hypothesis at work; [SRC] `06_Unitriangular.lean` `exists_approx_single`/`exists_approx` (the field version).
#### Generality decision
The contraction factor is `max q 2⁻¹` (not `q`) because the truncation error must be a fixed fraction `< 1` of `‖g‖` even when `q = 0`; no Tate hypothesis.

### [CLEANUP-21] Run `/cleanup` on `Unitriangular.lean`
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: T048, T049, T050 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Unitriangular.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [CLEANUP-ALL-5] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: CLEANUP-21, CLEANUP-19, CLEANUP-20 · **Parallel**: no · **Type**: cleanup
- **Description**: Pre-milestone sweep before M5. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T051] MILESTONE M5 — the unitriangular-perturbation criterion
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: CLEANUP-ALL-5 · **Parallel**: no · **Type**: milestone
- **Leaves**: L51.1–L51.3

#### Statement
```lean
theorem surjective_toCLM [IsTate R] : Surjective ha.toCLM := by
  sorry

theorem exists_linearIsometryEquiv [IsTate R] :
    ∃ T : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R),
      ∀ i j, matrixCoeff (T.toContinuousLinearEquiv : C₀(ℕ, R) →L[R] C₀(ℕ, R)) i j = a i j := by
  sorry

theorem IsOrthonormalBasis.of_isUnitriangularPerturbation {R : Type*} [NormedCommRing R]
    [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R] [CompleteSpace R] {M : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
    {e : ℕ → M} (he : IsOrthonormalBasis R e) {a : ℕ → ℕ → R} {q : ℝ}
    (ha : ZeroAtInftyContinuousMap.IsUnitriangularPerturbation a q) {f : ℕ → M}
    (hf : ∀ j, HasSum (fun i ↦ a i j • e i) (f j)) : IsOrthonormalBasis R f := by
  sorry
```
#### Proof sketch
1. `surjective_toCLM`: `ContinuousLinearMap.Ultra.surjective_of_forall_exists_approx ha.toCLM (q := max q 2⁻¹) (C := 1) (max_lt ha.q_lt_one (by norm_num))
   fun g ↦ by obtain ⟨f, hf, hfg⟩ := ha.exists_norm_sub_toCLM_le g; exact ⟨f, by rwa [one_mul], hfg⟩`.
2. `exists_linearIsometryEquiv`: `⟨ha.linearIsometryEquiv, fun i j ↦ ?_⟩`; the coerced map is `ha.toCLM` (`ContinuousLinearMap.ext fun _ ↦ rfl`), then `ha.matrixCoeff_toCLM i j`.
3. `IsOrthonormalBasis.of_isUnitriangularPerturbation`: `Φ := he.linearIsometryEquiv`, `T := ha.linearIsometryEquiv`, `Ψ := T.trans Φ`; for each `j`,
   `Ψ (single j 1) = Φ (ofTendsto (fun i ↦ a i j) _)` (the column: `coe_linearIsometryEquiv`, `toCLM`, `ofBounded_single`) `= ∑' i, a i j • e i = f j`
   (`linearIsometryEquiv_apply`, `(hf j).tsum_eq`); so `f = fun j ↦ Ψ.symm.symm (single j 1)` and `Ψ.symm.isOrthonormalBasis_symm_single` (T021) applies after `funext`.

#### Mathlib lemmas needed
`ContinuousLinearMap.Ultra.surjective_of_forall_exists_approx` (T048), `exists_norm_sub_toCLM_le` (T050), `matrixCoeff_toCLM`, `LinearIsometryEquiv.trans`, `LinearIsometryEquiv.isOrthonormalBasis_symm_single` (T021), `IsOrthonormalBasis.linearIsometryEquiv_apply` (T023), `ofBounded_single`, `HasSum.tsum_eq`.
#### Sources
[RM] §2.7.1–2.7.2 ("hence an isometric automorphism … if `e : ℕ → M` is a family in an orthonormalisable Banach module whose matrix in an orthonormal basis, after a reindexing by a bijection of `ℕ`, is a unitriangular perturbation, then `e` is an orthonormal basis. This is the form in which Amice's theorem (§4.4) is proved"); §2.7.3 (relation to [Col] Prop 1.1.5: no residue field needed).
#### Generality decision
`[IsTate R]` enters only through the successive-approximation helper (bounded `u`); the family criterion takes the expansions `hf` as hypotheses, so no coordinate functionals are needed (plan design).

### [CLEANUP-22] Run `/cleanup` on `Unitriangular.lean`
- **Status**: open · **File**: `Unitriangular.lean` · **Depends on**: T051 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Unitriangular.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T052] Examples: `C(ℤ_p, ℚ_p)` is orthonormalisable; the dual of `C₀(ℕ, ℚ_p)`; nonzero ON-able modules have unit vectors
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: CLEANUP-16, CLEANUP-19, CLEANUP-20, CLEANUP-22 · **Parallel**: no · **Type**: lemmas
- **Leaves**: L52.1–L52.3

#### Statement
```lean
theorem isONable_continuousMap_padic : IsONable ℚ_[p] C(ℤ_[p], ℚ_[p]) := by
  sorry

theorem nonempty_dual_linearIsometryEquiv_lp_padic :
    Nonempty ((C₀(ℕ, ℚ_[p]) →L[ℚ_[p]] ℚ_[p]) ≃ₗᵢ[ℚ_[p]] lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := by
  sorry

theorem _root_.Module.not_isONable_of_forall_norm_ne_one {R : Type*} [NormedRing R] [NormOneClass R]
    {M : Type*} [NormedAddCommGroup M] [Module R M] [Nontrivial M] (h : ∀ m : M, ‖m‖ ≠ 1) :
    ¬ IsONable R M := by
  sorry
```
#### Proof sketch
1. `isONable_continuousMap_padic`: `haveI := Padic.isRankOneDiscrete_valuation (p := p)`; `(Module.isONable_iff_forall_exists_norm_eq C(ℤ_[p], ℚ_[p])).2 fun g ↦ ?_`;
   `obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (continuous_norm.comp g.continuous).continuousOn`; `‖g‖ = ‖g x‖` by
   `le_antisymm ((ContinuousMap.norm_le g (norm_nonneg _)).2 fun y ↦ hx (Set.mem_univ y)) (g.norm_coe_le_norm x)`; `⟨g x, …⟩`.
2. `nonempty_dual_linearIsometryEquiv_lp_padic`: `⟨{ (dualEquivLp ℚ_[p] ℕ).toLinearEquiv with norm_map' := fun l ↦ (dualEquivLp ℚ_[p] ℕ).norm_map l }⟩` — the Ultra norm
   and Mathlib's norm on `C₀(ℕ, ℚ_[p]) →L[ℚ_[p]] ℚ_[p]` are the same function (Layer 1 `norm_eq_opNorm`, `rfl`), only the instances differ; if the elaborator
   rejects the `with`, build `LinearIsometryEquiv.mk` on the `LinearEquiv` with `norm_map'` by `show` + `rfl`-conversion.
3. `not_isONable_of_forall_norm_ne_one`: `rintro ⟨I, _, _, ⟨Φ⟩⟩`; `Nontrivial C₀(I, R)` from `Φ.symm.injective`/`Φ.surjective` and `Nontrivial M`; hence `Nonempty I`
   (an empty `I` makes `C₀(I, R)` a subsingleton, `eq_of_empty`); pick `i`, then `h (Φ.symm (single i 1))` contradicts `‖Φ.symm (single i 1)‖ = ‖single i 1‖ = ‖1‖ = 1`.

#### Mathlib lemmas needed
`Padic.isRankOneDiscrete_valuation` [NP], `Module.isONable_iff_forall_exists_norm_eq` (T032), `isCompact_univ`, `IsCompact.exists_isMaxOn`, `ContinuousMap.norm_le`, `ContinuousMap.norm_coe_le_norm`, `dualEquivLp` (T043), `ContinuousLinearMap.Ultra.norm_eq_opNorm` [L1], `ZeroAtInftyContinuousMap.eq_of_empty`, `norm_single`, `norm_one`.
#### Sources
[RM] Layer 2 Examples ("`C₀(ℕ, ℚ_p)` with its canonical basis and its dual `ℓ^∞(ℕ, ℚ_p)`; the Banach space `C(ℤ_p, ℚ_p)` is orthonormalisable (Layer 3 exhibits the basis, this layer only knows it from Serre's theorem)"); [Sch] Remark 10.2.
#### Generality decision
E28 for the dual example; `[NormOneClass R]` in the general lemma (`‖single i 1‖ = ‖1‖`).

### [T053] Examples: the doubled norm — potentially but not literally orthonormalisable
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: T052 · **Parallel**: no · **Type**: instances + lemmas
- **Leaves**: L53.1–L53.7

#### Statement
```lean
noncomputable instance : NormedAddCommGroup (Doubled K) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x ↦ 2 * ‖(toDoubled.symm x : K)‖
      map_zero' := by sorry
      add_le' := by sorry
      neg' := by sorry
      eq_zero_of_map_eq_zero' := by sorry }

instance : IsBoundedSMul K (Doubled K) := .of_norm_smul_le (by sorry)

instance [IsUltrametricDist K] : IsUltrametricDist (Doubled K) := by
  sorry

instance [CompleteSpace K] : CompleteSpace (Doubled K) := by
  sorry

theorem isPotentiallyONable [IsUltrametricDist K] [CompleteSpace K] :
    IsPotentiallyONable K (Doubled K) := by
  sorry

theorem not_isONable (hK : ∀ x : K, ‖x‖ ≠ 2⁻¹) : ¬ IsONable K (Doubled K) := by
  sorry

theorem not_isONable_doubled_padic (hp : p ≠ 2) : ¬ IsONable ℚ_[p] (NormedField.Doubled ℚ_[p]) := by
  sorry
```
#### Proof sketch
1. The `AddGroupNorm` fields: `map_zero'` by `simp`; `add_le'`: `2 * ‖x + y‖ ≤ 2 * ‖x‖ + 2 * ‖y‖` (`norm_add_le`, `mul_add`, `mul_le_mul_of_nonneg_left`);
   `neg'`: `norm_neg`; `eq_zero_of_map_eq_zero'`: `mul_eq_zero`, `norm_eq_zero` (`two_ne_zero`).
2. `IsBoundedSMul`: `.of_norm_smul_le fun c x ↦ le_of_eq (by rw [norm_def, norm_def, norm_smul]; ring)` (the action is `K` on itself).
3. `IsUltrametricDist`: `⟨fun x y z ↦ by simp only [dist_eq_norm, norm_def, ← mul_max_of_nonneg _ _ zero_le_two]; exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_sub_le_max? …) zero_le_two⟩`
   (use `IsUltrametricDist.dist_triangle_max` on `K` after rewriting `dist` as `2 * dist`).
4. `CompleteSpace`: Layer 0's `AddEquiv.completeSpace_congr_of_bounds` (`Module.lean` l. 80) applied to `toDoubled.toAddEquiv` with the bounds `‖toDoubled x‖ ≤ 2 * ‖x‖`
   and `‖x‖ ≤ 1 * ‖toDoubled x‖`-style (check its exact statement).
5. `isPotentiallyONable`: `IsONable K C₀(Unit, K)` (`isONable_zeroAtInfty`) transported along `(LinearIsometryEquiv.funUnique Unit K K).symm.trans piEquiv.symm`-type
   isometry `K ≃ₗᵢ[K] C₀(Unit, K)` (built in the proof), then `.isPotentiallyONable.of_continuousLinearEquiv` with the `≃L` given by `toDoubled` and the two bounds
   (`AddMonoidHomClass.continuous_of_bound`).
6. `not_isONable`: `Module.not_isONable_of_forall_norm_ne_one fun x hx ↦ hK (toDoubled.symm x) (by rw [norm_def] at hx; linarith? )` — from `2 * ‖y‖ = 1` get `‖y‖ = 2⁻¹`
   (`eq_inv_of_mul_eq_one_right`), contradiction.
7. `not_isONable_doubled_padic`: `NormedField.Doubled.not_isONable fun x hx ↦ ?_`; `x ≠ 0` (`norm_zero`, `inv_ne_zero`); `Padic.norm_eq_zpow_neg_valuation hx0` gives
   `(p : ℝ) ^ (-v) = 2⁻¹`, i.e. `(p : ℝ) ^ v = 2` (`zpow_neg`, `inv_inj`); with `3 ≤ p` (`hp.1.two_le`, `hp'`, `omega`): if `v ≤ 0` then `p ^ v ≤ 1 < 2`
   (`zpow_le_one_of_nonpos₀`), if `0 < v` then `3 ≤ p ≤ p ^ v` (`le_self_zpow`); `linarith`.

#### Mathlib lemmas needed
`AddGroupNorm.toNormedAddCommGroup`, `norm_add_le`, `norm_neg`, `norm_eq_zero`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul`, `mul_max_of_nonneg`, `IsUltrametricDist.dist_triangle_max`, `AddEquiv.completeSpace_congr_of_bounds` [L0], `isONable_zeroAtInfty` (T021), `LinearIsometryEquiv.funUnique`, `piEquiv` (T011), `AddMonoidHomClass.continuous_of_bound`, `Padic.norm_eq_zpow_neg_valuation`, `zpow_neg`, `Nat.Prime.two_le`, `zpow_le_one_of_nonpos₀`, `le_self_zpow`.
#### Sources
[RM] §2.3.5 ("for odd `p`, `ℂ_p` itself with the norm `2‖·‖` has no orthonormal basis, since `‖ℂ_p‖ = p^ℚ` does not contain `1/2`; the potential statement is §2.4") and Layer 2 Examples ("`ℂ_p` with the norm `2‖·‖` (`p` odd) is potentially but not literally orthonormalisable; a finite-dimensional `ℂ_p`-space with a norm whose values are not in `p^ℚ`"); E23.
#### Generality decision
The `ℂ_p` instances are terms already (`not_isONable_doubled_padicComplex` takes the value-group fact as a hypothesis, E23); the `ℚ_p` instance is proved outright.

### [T054] Examples: the shift and the two unitriangular perturbations
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: T052 · **Parallel**: yes (parallel with T053) · **Type**: definition + lemmas
- **Leaves**: L54.1–L54.4

#### Statement
```lean
noncomputable def shift : C₀(ℕ, R) →L[R] C₀(ℕ, R) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun n ↦ f (n + 1)) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    1 (by sorry)

theorem matrixCoeff_shift (i j : ℕ) : matrixCoeff (shift : C₀(ℕ, R) →L[R] C₀(ℕ, R)) i j =
    if j = i + 1 then 1 else 0 := by
  sorry

theorem isUnitriangularPerturbation_one_add (N : ℕ → ℕ → R) {q : ℝ} (hq : q < 1)
    (hN : ∀ i j, ‖N i j‖ ≤ q) (hlower : ∀ i j, ¬ j < i → N i j = 0)
    (hfin : ∀ j, {i | N i j ≠ 0}.Finite) :
    IsUnitriangularPerturbation (fun i j ↦ (if i = j then (1 : R) else 0) + N i j) q := by
  sorry

theorem isUnitriangularPerturbation_padicInt (a : ℕ → ℕ → ℤ_[p]) (hdiag : ∀ i, IsUnit (a i i))
    (hlow : ∀ i j, j < i → (p : ℤ_[p]) ∣ a i j) (hfin : ∀ j, {i | a i j ≠ 0}.Finite) :
    IsUnitriangularPerturbation a ((p : ℝ)⁻¹) := by
  sorry
```
#### Proof sketch
1. `shift`: tendsto `(tendsto_cofinite f).comp Nat.succ_injective.tendsto_cofinite`; `map_add'`/`map_smul'`: `ext; rfl`; the bound `1`:
   `norm_le_of_forall_le (by simp) fun n ↦ by rw [one_mul]; exact norm_apply_le f (n + 1)`.
2. `matrixCoeff_shift`: `simp [matrixCoeff, shift_apply, coe_single, Pi.single_apply, eq_comm]`.
3. `isUnitriangularPerturbation_one_add`: `hlower i i (lt_irrefl _)` gives `N i i = 0`; fields: `q_lt_one := hq`; `norm_le_one`: `by_cases i = j` (`‖1 + 0‖ = 1`;
   `‖0 + N i j‖ ≤ q ≤ 1` by `hq.le`); `diag_isUnit`: `isUnit_one` after simplification; `diag_isMultiplicative`: `IsMultiplicative.one`; `norm_diag`: `norm_one`;
   `norm_lower_le`: `‖0 + N i j‖ ≤ q` (`if_neg (ne_of_gt h)`); `column_finite`: `(Set.finite_singleton j ∪ hfin j).subset` (`Set.Finite.union`, case analysis).
4. `isUnitriangularPerturbation_padicInt`: `norm_le_one := fun i j ↦ PadicInt.norm_le_one _`; `diag_isUnit := hdiag`; `diag_isMultiplicative := fun i ↦ isMultiplicative_of_normMulClass _`
   (or `fun i x ↦ PadicInt.norm_mul _ _`); `norm_diag := fun i ↦ PadicInt.isUnit_iff.1 (hdiag i)`; `norm_lower_le := fun i j h ↦ by simpa using (PadicInt.norm_le_pow_iff_dvd _ 1).2 (by simpa using hlow i j h)`;
   `column_finite := hfin`; `q_lt_one`: `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)`.

#### Mathlib lemmas needed
`Nat.succ_injective`, `Function.Injective.tendsto_cofinite`, `Pi.single_apply`, `isUnit_one`, `NormedRing.IsMultiplicative.one` [L0], `Set.finite_singleton`, `Set.Finite.union`, `Set.Finite.subset`, `PadicInt.norm_le_one`, `PadicInt.isUnit_iff`, `PadicInt.norm_le_pow_iff_dvd`, `NormedRing.isMultiplicative_of_normMulClass` [L0], `inv_lt_one_of_one_lt₀`, `Nat.Prime.one_lt`.
#### Sources
[RM] Layer 2 Examples ("the matrix of the shift on `C₀(ℕ, R)`; the unitriangular perturbation `1 + N` with `N` strictly lower triangular of norm `q`, and a matrix with entries in `ℤ_p`, unit diagonal, and lower entries in `pℤ_p`").
#### Generality decision
The `ℤ_p` example has level `p⁻¹`, the sharpest possible (`‖p‖ = p⁻¹`).

### [CLEANUP-23] Run `/cleanup` on `ModelSpace/Examples.lean`
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: T052, T053, T054 · **Parallel**: no · **Type**: cleanup
- **Description**: Three proof tickets landed on `Examples.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T055] Example: the counterexample to §2.6.4 without closedness
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: CLEANUP-23 · **Parallel**: no · **Type**: instance + definition + lemmas
- **Leaves**: L55.1–L55.4

#### Statement
```lean
instance : IsTate (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := by
  sorry

noncomputable def geomDelta : C₀(ℕ, lp (fun _ : ℕ ↦ ℚ_[p]) ∞) :=
  ofTendsto (fun n ↦ (p : ℚ_[p]) ^ n • lp.single ∞ n (1 : ℚ_[p])) (by sorry)

theorem not_isClosed_span_geomDelta :
    ¬ IsClosed (Submodule.span (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) {geomDelta p} :
      Set C₀(ℕ, lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) := by
  sorry

theorem exists_truncation_far_geomDelta (S : Finset ℕ) :
    ∃ f ∈ Submodule.span (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) {geomDelta p},
      2⁻¹ * ‖f‖ < ‖truncation (↑S : Set ℕ) f - f‖ := by
  sorry
```
#### Proof sketch
1. `IsTate`: the constant sequence `(p : lp …)` (`Nat.cast`) is a unit with inverse the constant `p⁻¹` (`memℓp_infty` bounded; `Units.mkOfMulEqOne`, `lp.ext`,
   `lp.infty_coeFn_mul`, `mul_inv_cancel₀`); multiplicative: `(p : lp …) * x = (p : ℚ_[p]) • x` (`lp.ext`, `lp.infty_coeFn_mul`, `lp.coeFn_smul`), so
   `‖p * x‖ = ‖(p : ℚ_[p])‖ * ‖x‖` (`lp.norm_const_smul ENNReal.top_ne_zero`) and `‖(p : lp …)‖ = ‖(p : ℚ_[p])‖` (`lp.norm_eq_ciSup`, `ciSup_const`);
   `‖(p : ℚ_[p])‖ = p⁻¹ < 1` (`Padic.norm_p`, `inv_lt_one_of_one_lt₀`).
2. `geomDelta`'s tendsto: `‖(p : ℚ_[p]) ^ n • lp.single ∞ n 1‖ = ‖p‖ ^ n` (`lp.norm_const_smul`, `norm_pow`, `‖lp.single ∞ n 1‖ = 1` via `lp.norm_eq_ciSup` and
   `lp.single_apply`), `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Nat.cofinite_eq_atTop`.
3. `not_isClosed_span_geomDelta`: `g := ofTendsto (fun n ↦ (p : ℚ_[p]) ^ ((n + 1) / 2) • lp.single ∞ n 1) _` (same tendsto). (a) `g ∈ closure (span {geomDelta p})`:
   `truncation (Set.Iic k) g = rₖ • geomDelta p` with `rₖ := ∑ n ∈ Finset.range (k + 1), (p : ℚ_[p]) ^ (((n + 1) / 2 : ℕ) - n : ℤ) • lp.single ∞ n 1 ∈ lp …`
   (`lp.ext`, coordinates: `lp.single_apply`, `δₙ * δₙ = δₙ`, `zpow_add₀`), in the span (`Submodule.smul_mem`, `Submodule.mem_span_singleton_self`), and
   `truncation (Set.Iic k) g → g` (`tendsto_truncation_finset` along `Finset.range (k+1)`, or `norm_sub_truncation_le` directly); `mem_closure_of_tendsto`.
   (b) `g ∉ span {geomDelta p}`: `Submodule.mem_span_singleton` gives `r` with `r • geomDelta p = g`; comparing coordinates at `n` and evaluating at `n`
   (`lp.coeFn_smul`, `lp.infty_coeFn_mul`, `lp.single_apply`): `r n * p ^ n = p ^ ((n + 1) / 2)`, so `‖r n‖ = p ^ (n - (n + 1) / 2)` (`Padic.norm_p`, `norm_pow`,
   `norm_zpow`), unbounded in `n` (take `n := 2 m`, `‖r n‖ = p ^ m`), contradicting `‖r n‖ ≤ ‖r‖` (`lp.norm_apply_le_norm`) with `p ^ m → ∞`
   (`tendsto_pow_atTop_atTop_of_one_lt`); hence `IsClosed` fails (`IsClosed.closure_eq`, `Submodule.topologicalClosure_coe`).
4. `exists_truncation_far_geomDelta`: `m := S.sup id + 1`, `m ∉ S` (`Finset.le_sup (f := id)`, `Nat.lt_irrefl`); `f := lp.single ∞ m 1 • geomDelta p`
   (`Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`); `f n = if n = m then (p : ℚ_[p]) ^ m • lp.single ∞ m 1 else 0` (`lp.single_apply`, `mul_ite`);
   `‖f‖ = ‖(p : ℚ_[p])‖ ^ m` (`exists_norm_apply_eq_norm`/`norm_single`-style computation) `> 0`; `truncation ↑S f = 0` (`ext n`, `truncation_apply`: `n ∈ S ⟹ n ≠ m`);
   so `‖truncation ↑S f - f‖ = ‖f‖ > 2⁻¹ * ‖f‖` (`norm_neg`, `half_lt_self`).

#### Mathlib lemmas needed
`memℓp_infty`, `Units.mkOfMulEqOne`, `lp.ext`, `lp.infty_coeFn_mul`, `lp.coeFn_smul`, `lp.norm_const_smul`, `lp.norm_eq_ciSup`, `lp.single`, `lp.single_apply`, `lp.norm_apply_le_norm`, `ciSup_const`, `Padic.norm_p`, `inv_lt_one_of_one_lt₀`, `norm_pow`, `norm_zpow`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_pow_atTop_atTop_of_one_lt`, `Nat.cofinite_eq_atTop`, `Submodule.mem_span_singleton`, `Submodule.mem_span_singleton_self`, `mem_closure_of_tendsto`, `Submodule.topologicalClosure_coe`, `lp.instIsUltrametricDist` [L1], `truncation_apply`, `norm_sub_truncation_le` (T014).
#### Sources
[RM] §2.6.4 ("⚠ Without closedness the statement is false; record the counterexample"); Layer 1 Examples (`ℓ^∞(ℕ, ℚ_p)` as the non-Noetherian Banach–Tate ring, E18); the construction is the plan's (R = `ℓ^∞(ℕ, ℚ_p)`, `v(n) = pⁿ δₙ`, `P = R·v`).
#### Generality decision
The ring `lp (fun _ : ℕ ↦ ℚ_[p]) ∞` has `NormedCommRing`, `NormOneClass`, `CompleteSpace` (Mathlib) and `IsUltrametricDist` (Layer 1); the `IsTate` instance is new.

### [CLEANUP-24] Run `/cleanup` on `ModelSpace/Examples.lean`
- **Status**: open · **File**: `ModelSpace/Examples.lean` · **Depends on**: T055 · **Parallel**: no · **Type**: cleanup
- **Description**: Final cleanup of `Examples.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T056] Integration: chain root, full build, axioms, linter, README check
- **Status**: open · **File**: `project` · **Depends on**: CLEANUP-24, CLEANUP-14, CLEANUP-16 · **Parallel**: no · **Type**: integration
- **Leaves**: L56.1–L56.4

#### Statement
```lean
(no Lean declaration — an edit of `PhD/TauCeti.lean`, the README, and the verification sweep)
```
#### Proof sketch
1. Add `import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples` to `PhD/TauCeti.lean` (alphabetically before `…PadicFunctionalAnalysis.NormComparison`).
2. `lake build PhD.TauCeti` (the whole chain, including the RAG dependents of T001); zero errors, no `sorry` warnings in the fourteen Layer 2 files.
3. `python3 .mathlib-quality/tauceti-pfa-layer2/scratch/axioms.py` adapted to the fourteen modules (every declaration: only `propext`, `Classical.choice`, `Quot.sound`);
   `lake exe runLinter PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` for each module; fix findings inline.
4. The README errata (E19–E24, E27) were applied at plan review on 2026-10-06; check that the Lean names mentioned there still match the code
   (`Module.IsONable`, `IsTOrthogonalFamily`, `ZeroAtInftyContinuousMap.*`) and fix the prose if a name changed during execution.

#### Mathlib lemmas needed
none (tooling).
#### Sources
[RM] Layer 2; plan.md errata table.
#### Generality decision
The chain-separation rule and the one-Lean-process rule apply; commit only when the user asks.

### [CLEANUP-FINAL] Run `/cleanup-all` on the project
- **Status**: open · **File**: the project · **Depends on**: T056 · **Parallel**: no · **Type**: cleanup
- **Description**: Final `/cleanup-all` of the Layer 2 files. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).
