# Ticket board: Tau Ceti `NewtonPolygons`, Layer 1 (additive valuations of a nonarchimedean field)

**Board**: `.mathlib-quality/tauceti-np-layer1/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and `tauceti-np-layer0/` is the finished Layer 0).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1 (§1.1–§1.5, Examples) — cited as [RM].
**Code**: `PhD/TauCeti/Code/NewtonPolygons/AddVal/` (`NegLog`, `RatLog`, `Basic`, `RankOne`, `Commensurable`,
`Discrete`, `Normed`, `Padic`, `LaurentSeries`, `Extension`, `PadicComplex`, `Examples`) — 12 files, module
prefix `PhD.TauCeti.Code.NewtonPolygons.AddVal`; the chain root `PhD/TauCeti.lean` imports the leaf
`AddVal.Examples`. Planned 2026-10-06.
**Status**: **COMPLETE 2026-10-06** — every ticket done in one `/beastmode` session: all 144 declarations are
proved, the twelve modules pass `lake exe runLinter`, no line exceeds 100 characters, and every declaration
(including the five milestones) depends only on `propext`, `Classical.choice`, `Quot.sound`
(`scratch/axioms.py`). No hypothesis was added and no conclusion changed; `@[simp]` attributes and two unused instances were removed
on the linter's advice (`plan.md`, "Execution notes"). `b2_log.jsonl` is empty.
**Name check**: every Mathlib name in the "Mathlib lemmas needed" blocks elaborates against the pin
(`scratch/names_tickets_mathlib.lean`, 0 errors) and every skeleton name (`scratch/signatures.lean`, 0 errors);
see `plan.md`, "Name check".

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 52 (`T001`–`T052`; `T052` is the chain-root gate) |
| Per-file cleanups | 21 (`CLEANUP-1`–`CLEANUP-21`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **79** |

- Open: 0 | In Progress: 0 | Done: 79.
- Coverage: every open declaration of the skeleton (144, 152 `sorry`s) is named in exactly one ticket
  (the generator `scratch/gen_tickets.py` fails otherwise).
- **Milestone M1** = `T009`: `Valuation.addVal_map` — the §1.1 dictionary complete, with its naturality.
- **Milestone M2** = `T017`: `Valuation.addValQ_unique` — the element pins the valuation ([RM] §1.4.4).
- **Milestone M3** = `T035`: `NormedField.normAddValZ_padic` — `normAddValZ ℚ_[p] = Padic.addValuation`
  ([RM] §1.3.5).
- **Milestone M4** = `T042`: `NormedField.normAddValZ_algebraMap` — the ramification formula ([RM] §1.3.6).
- **Milestone M5** = `T048`: `PadicComplex.range_normAddValQ` (with `isCommensurable_p`) — the value group of
  `ℂ_p` is `p^ℚ` ([RM] §1.5.4–§1.5.5).
- Parallel capacity: 2 at the start (`NegLog.lean` ∥ `RatLog.lean`), 2 after `Discrete.lean`
  (`LaurentSeries.lean` ∥ `Normed.lean`), 2 after `Normed.lean` (`Padic.lean` ∥ `Extension.lean`); on this
  machine run one Lean process at a time, so the honest estimate is one worker.

Conventions binding every ticket (see `plan.md`, "Generality and design decisions"): the [PR] names of
mathlib4#43578/#43580 for §1.1; `IsCommensurable` is a `Prop` class on `(v, π)`; rings wherever [SRC] allowed
it; `WithTop.map` for rescaled valuations; no `import PhD.Main.*` — the Main-chain files are read-only
proof references, cited as [SRC] (port with the new names, never copy-import). Deviations D1–D6 from the
roadmap text are recorded in `plan.md` and are not to be "fixed" by a worker.

Worker protocol: `/beastmode` inline as the main agent (user preference); after each ticket
`lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.<File>` and `#print axioms` on each declaration (only
`propext`, `Classical.choice`, `Quot.sound`); mark `done` only with zero `sorry` in the ticket's
declarations; append a `Progress` line to the ticket with a timestamp; record any statement repair in
`b2_log.jsonl`.

## Dependency order (ticket groups)

```text
G1 NegLog        : T001 → T002 → T003 → CLEANUP-1 → T004 → CLEANUP-2
G2 RatLog        : T005 → T006 → CLEANUP-3                                   (∥ G1)
G3 Basic         : T007 → T008 → CLEANUP-ALL-1 → T009 [M1] → CLEANUP-4      (after CLEANUP-2)
G4 RankOne       : T010 → T011 → CLEANUP-5                                   (after CLEANUP-4)
G5 Commensurable : T012 → T013 → T014 → CLEANUP-6 → T015 → T016 → CLEANUP-ALL-2 → T017 [M2] → CLEANUP-7
                   → T018 → T019 → CLEANUP-8                                 (after CLEANUP-3, CLEANUP-5)
G6 Discrete      : T020 → T021 → T022 → CLEANUP-9 → T023 → T024 → CLEANUP-10 (after CLEANUP-8)
G7 Normed        : T025 → T026 → T027 → CLEANUP-11 → T028 → T029 → T030 → CLEANUP-12 → T031 → CLEANUP-13
                                                                             (after CLEANUP-10)
G8 Padic         : T032 → T033 → T034 → CLEANUP-14 → CLEANUP-ALL-3 → T035 [M3] → CLEANUP-15
                                                                             (after CLEANUP-13)
G9 LaurentSeries : T036 → T037 → T038 → CLEANUP-16                           (after CLEANUP-10; ∥ G7)
G10 Extension    : T039 → T040 → T041 → CLEANUP-17 → CLEANUP-ALL-4 → T042 [M4] → T043 → T044 → CLEANUP-18
                                                                             (after CLEANUP-13; ∥ G8)
G11 PadicComplex : T045 → T046 → T047 → CLEANUP-19 → CLEANUP-ALL-5 → T048 [M5] → CLEANUP-20
                                                                             (after CLEANUP-15, CLEANUP-18)
G12 Examples     : T049 → T050 → T051 → CLEANUP-21                           (after CLEANUP-16, CLEANUP-20)
G13 gate         : T052 → CLEANUP-FINAL                                      (after every final cleanup)
```

---

## Tickets

### [T001] `negLog`: zero, exp, one, `eq_top`, `eq_coe`, multiplicativity
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: none · **Parallel**: yes (with T005) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC] (`rfl` for zero/exp; `expRecOn` inductions; `coe_neg` excluded from simp in `negLog_eq_top`); module builds, std axioms.
- **Leaves**: L1.1–L1.6

#### Statement
```lean
@[simp] lemma negLog_zero : negLog (0 : Mᵐ⁰) = ⊤ := by sorry
@[simp] lemma negLog_exp (m : M) : negLog (exp m) = ((-m : M) : WithTop M) := by sorry
@[simp] lemma negLog_eq_top {x : Mᵐ⁰} : negLog x = ⊤ ↔ x = 0 := by sorry
@[simp] lemma negLog_one : negLog (1 : Mᵐ⁰) = 0 := by sorry
lemma negLog_eq_coe {x : Mᵐ⁰} {m : M} : negLog x = (m : WithTop M) ↔ x = exp (-m) := by sorry
lemma negLog_mul (x y : Mᵐ⁰) : negLog (x * y) = negLog x + negLog y := by sorry
```
#### Proof sketch
1. `negLog_zero`, `negLog_exp`: `rfl` — `negLog` is `expRecOn x ⊤ (fun m ↦ ↑(-m))` and `expRecOn` computes on
   the constructors `0` (= `none`) and `exp m` (= `↑(ofAdd m)`) definitionally (`WithZero.expRecOn_zero`,
   `WithZero.expRecOn_exp` are `rfl`).
2. `negLog_eq_top`: `induction x using WithZero.expRecOn with | zero => simp | exp a => simp
   [-WithTop.LinearOrderedAddCommGroup.coe_neg]`. ⚠ Exclude `coe_neg`: otherwise simp rewrites `↑(-a)` to
   `-↑a` and no longer sees `WithTop.coe_ne_top`. In the `exp` case both sides are false
   (`WithTop.coe_ne_top`, `WithZero.exp_ne_zero`).
3. `negLog_one`: `rw [← WithZero.exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]`.
4. `negLog_eq_coe`: `induction x using WithZero.expRecOn`; zero case: `exact ⟨fun h ↦ absurd h (by simp),
   fun h ↦ absurd h.symm WithZero.exp_ne_zero⟩`; exp case: `rw [negLog_exp, WithTop.coe_inj, WithZero.exp_inj,
   neg_eq_iff_eq_neg]`.
5. `negLog_mul`: double `expRecOn` induction; the two zero cases close by `simp` (`WithTop.top_add`,
   `WithTop.add_top`, `zero_mul`, `mul_zero`); the exp–exp case: `rw [← WithZero.exp_add, negLog_exp, negLog_exp,
   negLog_exp, neg_add, WithTop.coe_add]`.
[SRC] `PhD/Main/ForMathlib/Algebra/Order/GroupWithZero/WithZero.lean`, lemmas of the same names.
#### Mathlib lemmas needed
`WithZero.expRecOn`, `WithZero.expRecOn_zero`, `WithZero.expRecOn_exp`, `WithZero.exp_ne_zero`, `WithZero.exp_zero`, `WithZero.exp_inj`, `WithZero.exp_add`, `WithTop.coe_ne_top`, `WithTop.coe_zero`, `WithTop.coe_inj`, `WithTop.coe_add`, `WithTop.top_add`, `WithTop.add_top`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `neg_eq_iff_eq_neg`, `neg_add`, `neg_zero`.
#### Sources
[RM] §1.1.1 (Q1.1), [PR] #43578 (Q1.6), [BGR] 1.5.2 (Q1.5); decomposition L1.1–L1.6. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
Any `[AddCommGroup M]`; no order needed for these six (the order enters at T002). Universe-polymorphic.

### [T002] `negLog` reverses the order; the isomorphism `orderAddIsoWithTop`
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: T001 · **Parallel**: yes (with T005, T006) · **Type**: lemmas + def fields
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `negLog_lt_negLog` = `lt_iff_lt_of_le_iff_le negLog_le_negLog`; `orderAddIsoWithTop` fields ported (`map_add' := negLog_mul`, `map_le_map_iff' := negLog_le_negLog`).
- **Leaves**: L1.7–L1.10

#### Statement
```lean
lemma negLog_le_negLog {x y : Mᵐ⁰} : negLog x ≤ negLog y ↔ y ≤ x := by sorry
lemma negLog_lt_negLog {x y : Mᵐ⁰} : negLog x < negLog y ↔ y < x := by sorry
def orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M where
  toFun x := negLog x
  invFun y := y.recTopCoe (0 : Mᵐ⁰) fun m ↦ exp (-m)
  left_inv x := by sorry
  right_inv y := by sorry
  map_add' x y := by sorry
  map_le_map_iff' := by sorry
@[simp] lemma orderAddIsoWithTop_apply (x : (Additive Mᵐ⁰)ᵒᵈ) :
    orderAddIsoWithTop M x = negLog x := by sorry
```
#### Proof sketch
1. `negLog_le_negLog`: double `expRecOn` induction. zero–any: `simp` (`le_top` on the left, `zero_le'` on the
   right). exp–zero: `simp` (`↑(-a) ≤ ⊤` true, `0 ≤ exp b` true). exp–exp: `rw [negLog_exp, negLog_exp,
   WithTop.coe_le_coe, neg_le_neg_iff, WithZero.exp_le_exp]`.
2. `negLog_lt_negLog`: `lt_iff_lt_of_le_iff_le negLog_le_negLog` (the `≤` lemma with the roles of `x, y`
   swapped gives the strict version on a linear order).
3. `orderAddIsoWithTop` fields: `left_inv x`: `induction x using WithZero.expRecOn with | zero => rfl | exp a =>
   show WithZero.exp (- -a) = WithZero.exp a; rw [neg_neg]`. `right_inv y`: `induction y using WithTop.recTopCoe
   with | top => rfl | coe m => show negLog (WithZero.exp (-m)) = (m : WithTop M); rw [negLog_exp, neg_neg]`.
   `map_add' := negLog_mul`. `map_le_map_iff' := negLog_le_negLog`. (After this the def's signature gains
   `[IsOrderedAddMonoid M]`, as intended — see decomposition L1.9.)
4. `orderAddIsoWithTop_apply`: `rfl`.
[SRC] `negLog_le_negLog`, `negLogOrderAddIso`, `negLogOrderAddIso_apply`.
#### Mathlib lemmas needed
`WithZero.exp_le_exp`, `WithTop.coe_le_coe`, `WithTop.recTopCoe`, `neg_le_neg_iff`, `neg_neg`, `le_top`, `zero_le'`, `lt_iff_lt_of_le_iff_le`.
#### Sources
[RM] §1.1.1 (Q1.1), [PR] #43578 (Q1.6); decomposition L1.7–L1.10. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]` — exactly the instances `WithZero.exp_le_exp` needs.

### [T003] `mapAddHom'`: value on `exp`, strict monotonicity, naturality of `negLog`
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: T002 · **Parallel**: yes (with T005, T006) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `mapAddHom'_exp` is `rfl`; strict monotonicity via `WithZero.map'_strictMono`; naturality by `expRecOn`.
- **Leaves**: L1.11–L1.13

#### Statement
```lean
@[simp] lemma mapAddHom'_exp (f : M →+ N) (m : M) : mapAddHom' f (exp m) = exp (f m) := by sorry
lemma mapAddHom'_strictMono [Preorder M] [Preorder N] {f : M →+ N} (hf : StrictMono f) :
    StrictMono (mapAddHom' f) := by sorry
lemma negLog_mapAddHom' (f : M →+ N) (x : Mᵐ⁰) :
    negLog (mapAddHom' f x) = WithTop.map f (negLog x) := by sorry
```
#### Proof sketch
1. `mapAddHom'_exp`: `rfl` (`WithZero.map'_coe`; `AddMonoidHom.toMultiplicative f (ofAdd m) = ofAdd (f m)`
   definitionally).
2. `mapAddHom'_strictMono`: `WithZero.map'_strictMono fun _ _ h ↦ hf h` — the Mathlib lemma takes strict
   monotonicity of the underlying `Multiplicative M →* Multiplicative N` hom, which is `hf` read through the
   type synonyms.
3. `negLog_mapAddHom'`: `induction x using WithZero.expRecOn with | zero => rfl | exp a => rw [mapAddHom'_exp,
   negLog_exp, negLog_exp, WithTop.map_coe, map_neg]` (zero case: `map_zero` and `WithTop.map_top` are both
   `rfl`).
[SRC] `expMap_exp`, `expMap_strictMono`, `negLog_expMap`.
#### Mathlib lemmas needed
`WithZero.map'`, `WithZero.map'_coe`, `WithZero.map'_strictMono`, `AddMonoidHom.toMultiplicative`, `WithTop.map_coe`, `WithTop.map_top`, `map_neg`, `map_zero`.
#### Sources
[RM] §1.1.2 (Q1.2), [PR] #43578 (Q1.6); decomposition L1.11–L1.13. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[AddCommGroup M] [AddCommGroup N]`, plus `[Preorder M] [Preorder N]` for the monotonicity statement only.

### [CLEANUP-1] Run /cleanup on `NegLog.lean`
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T004] The real line: `NNReal.toRealMultZero` and `WithZeroMulReal.toNNReal`
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: CLEANUP-1 · **Parallel**: yes (with T005, T006) · **Type**: def fields + lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `toRealMultZero`, `toNNReal` ported verbatim from [SRC] `Data/Real/WithZero.lean` (the `lift … to ℝ` route works).
- **Leaves**: R3/R4 inputs (`toRealMultZero_strictMono`, `toNNReal_exp`, `toNNReal_strictMono`)

#### Statement
```lean
noncomputable def toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰ where
  toFun x := if x = 0 then 0 else WithZero.exp (Real.log x)
  map_zero' := by sorry
  map_one' := by sorry
  map_mul' x y := by sorry
lemma toRealMultZero_of_ne_zero {x : ℝ≥0} (hx : x ≠ 0) :
    toRealMultZero x = WithZero.exp (Real.log x) := by sorry
lemma toRealMultZero_strictMono : StrictMono toRealMultZero := by sorry
noncomputable def toNNReal {e : ℝ≥0} (he : e ≠ 0) : ℝᵐ⁰ →*₀ ℝ≥0 where
  toFun x := if x = 0 then 0 else e ^ (log x)
  map_zero' := by sorry
  map_one' := by sorry
  map_mul' x y := by sorry
@[simp] lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (t : ℝ) : toNNReal he (exp t) = e ^ t := by sorry
lemma toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (toNNReal (ne_zero_of_lt he)) := by sorry
```
#### Proof sketch
1. `toRealMultZero` fields: `map_zero' := if_pos rfl`; `map_one'`: `rw [if_neg one_ne_zero]; simp`
   (`NNReal.coe_one`, `Real.log_one`, `WithZero.exp_zero`); `map_mul' x y`: `rcases eq_or_ne x 0 with rfl | hx`
   (`simp`), same for `y`, then `rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, ← WithZero.exp_add,
   NNReal.coe_mul, Real.log_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]`.
2. `toRealMultZero_of_ne_zero`: `if_neg hx`.
3. `toRealMultZero_strictMono`: `intro x y hxy`; `hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'`; if `x = 0`:
   `rw [map_zero, toRealMultZero_of_ne_zero hy]; exact WithZero.exp_pos`; else `rw [toRealMultZero_of_ne_zero hx,
   toRealMultZero_of_ne_zero hy, WithZero.exp_lt_exp]; exact Real.log_lt_log (by exact_mod_cast hx.bot_lt)
   (by exact_mod_cast hxy)`.
4. `toNNReal` fields: `map_zero' := if_pos rfl`; `map_one'`: `rw [if_neg one_ne_zero, WithZero.log_one,
   NNReal.rpow_zero]`; `map_mul'`: cases on `x = 0`, `y = 0` (`simp`), then `rw [if_neg (mul_ne_zero hx hy),
   if_neg hx, if_neg hy, WithZero.log_mul hx hy, NNReal.rpow_add he]`.
5. `toNNReal_exp`: `simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg WithZero.exp_ne_zero,
   WithZero.log_exp]`.
6. `toNNReal_strictMono`: `intro x y hxy`; `hy : y ≠ 0`; `x = 0`: `lift y to ℝ using hy with t; rw [map_zero,
   toNNReal_exp]; exact NNReal.rpow_pos (zero_lt_one.trans he)`; else `lift x to ℝ using hx with s; lift y to ℝ
   using hy with t; rw [toNNReal_exp, toNNReal_exp]; exact NNReal.rpow_lt_rpow_of_exponent_lt he
   (WithZero.exp_lt_exp.mp hxy)` (the `lift` uses the `CanLift ℝᵐ⁰ ℝ exp (· ≠ 0)` instance; if it is not
   available, use `WithZero.exp_log hx` to rewrite `x = exp (log x)` instead).
[SRC] `PhD/Main/ForMathlib/Data/Real/WithZero.lean`.
#### Mathlib lemmas needed
`WithZero.exp_add`, `WithZero.exp_pos`, `WithZero.exp_lt_exp`, `WithZero.exp_log`, `WithZero.log_exp`, `WithZero.log_one`, `WithZero.log_mul`, `WithZero.exp_ne_zero`, `NNReal.coe_mul`, `NNReal.coe_one`, `NNReal.rpow_zero`, `NNReal.rpow_add`, `NNReal.rpow_pos`, `NNReal.rpow_lt_rpow_of_exponent_lt`, `Real.log_mul`, `Real.log_lt_log`, `Real.log_one`, `MonoidWithZeroHom.coe_mk`, `ZeroHom.coe_mk`, `bot_le`, `mul_ne_zero`.
#### Sources
[RM] §1.2.1 (the `ℝᵐ⁰`-valued valuation needs `ℝ≥0 →*₀ ℝᵐ⁰`) and §1.4.5 (`e ^ ·` for the rank-one structure); Mathlib's `WithZeroMulInt.toNNReal` is the integer model; decomposition R3/R4 inputs. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`toNNReal` for any base `e ≠ 0` (strict monotonicity only for `1 < e`), as `WithZeroMulInt.toNNReal`.

### [CLEANUP-2] Run /cleanup on `NegLog.lean`
- **Status**: done (2026-10-06) · **File**: `NegLog.lean` · **Depends on**: T004 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T005] The `ℚ`-valued logarithm of a rank-one ordered group: well-definedness, additivity, normalisation
- **Status**: done (2026-10-06) · **File**: `RatLog.lean` · **Depends on**: none · **Parallel**: yes (with T001–T004) · **Type**: lemma + def fields + lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC] `Commensurable.lean` (group level); builds, std axioms.
- **Leaves**: L2.1–L2.4

#### Statement
```lean
private lemma ratCoeff_eq (h : ∀ a : M, IsCommensurableWith a₀ a) (ha₀ : a₀ ≠ 0)
    {m n : ℤ} (hn : 0 < n) (hmn : n • a = m • a₀) : ratCoeff h a = (m : ℚ) / (n : ℚ) := by sorry
noncomputable def ratLog (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :
    M →+ ℚ where
  toFun a := -ratCoeff h a
  map_zero' := by sorry
  map_add' a b := by sorry
lemma ratLog_eq (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) {m n : ℤ}
    (hn : 0 < n) (hmn : n • a = m • a₀) : ratLog ha₀ h a = -((m : ℚ) / (n : ℚ)) := by sorry
@[simp] lemma ratLog_self (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :
    ratLog ha₀ h a₀ = -1 := by sorry
```
#### Proof sketch
1. `ratCoeff_eq` (independence of the witness): `obtain ⟨hn', hmn'⟩ := (h a).choose_spec.choose_spec`;
   `set m' := (h a).choose`, `set n' := (h a).choose_spec.choose`; `key : (n' * m - n * m') • a₀ = 0` by the `calc`
   `(n' * m) • a₀ = n' • (m • a₀) = n' • (n • a) = (n' * n) • a = (n * n') • a = n • (n' • a) = n • (m' • a₀) = (n * m') •
   a₀` (`mul_smul`, `hmn`, `hmn'`, `mul_comm`), then `sub_smul`, `sub_eq_zero`; `key' : m * n' = m' * n` from
   `IsAddTorsionFree.zsmul_eq_zero_iff_left ha₀` (ordered groups are torsion-free: the instance is found);
   finish with `div_eq_div_iff` and `exact_mod_cast key'.symm`.
2. `ratLog.map_zero'`: `rw [ratCoeff_eq h ha₀.ne (m := 0) (n := 1) one_pos (by simp), Int.cast_zero, zero_div,
   neg_zero]`. `map_add' a b`: witnesses `⟨m₁, n₁, hn₁, e₁⟩ := h a`, `⟨m₂, n₂, hn₂, e₂⟩ := h b`; `e : (n₁ * n₂) •
   (a + b) = (n₂ * m₁ + n₁ * m₂) • a₀` by `smul_add, add_smul` and `mul_smul` with `e₁, e₂`; then three
   `ratCoeff_eq` rewrites, `push_cast`, `field_simp`, `ring`.
3. `ratLog_eq`: `congrArg Neg.neg (ratCoeff_eq h ha₀.ne hn hmn)`.
4. `ratLog_self`: `rw [ratLog_eq ha₀ h (m := 1) (n := 1) one_pos (by simp)]; norm_num`.
[SRC] `PhD/Main/ForMathlib/Algebra/Order/Group/Commensurable.lean`.
#### Mathlib lemmas needed
`mul_smul`, `sub_smul`, `sub_eq_zero`, `smul_add`, `add_smul`, `IsAddTorsionFree.zsmul_eq_zero_iff_left`, `div_eq_div_iff`, `Int.cast_zero`, `zero_div`, `neg_zero`, `one_pos`, `mul_comm`.
#### Sources
[RM] §1.4.2 (Q2.1) and convention 3 (Q2.2); the well-definedness argument of decomposition R2; decomposition L2.1–L2.4. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
Any `[AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]`; `a₀ < 0` (the sign makes `ratLog` increasing, [RM] convention 6).

### [T006] `ratLog` is strictly monotone and unique
- **Status**: done (2026-10-06) · **File**: `RatLog.lean` · **Depends on**: T005 · **Parallel**: yes (with T001–T004) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): strict monotonicity ported; `ratLog_unique` new: `n • g a = -m` via `map_zsmul`, then `mul_div_cancel_left₀`.
- **Leaves**: L2.5, L2.6

#### Statement
```lean
lemma ratLog_strictMono (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :
    StrictMono (ratLog ha₀ h) := by sorry
lemma ratLog_unique (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) (g : M →+ ℚ)
    (hg : g a₀ = -1) : g = ratLog ha₀ h := by sorry
```
#### Proof sketch
1. `ratLog_strictMono`: first `key : ∀ a, 0 < a → 0 < ratLog ha₀ h a`: witnesses `⟨m, n, hn, hmn⟩ := h a`;
   `rw [ratLog_eq ha₀ h hn hmn, neg_pos]`; `hna : 0 < m • a₀` from `hmn ▸ (zsmul_lt_zsmul_iff_left ha).mpr hn`
   (with `0 • a = 0`); `hm : m < 0` by `lt_trichotomy m 0` (the `m = 0` case contradicts `hna` by `simp`; the
   `0 < m` case gives `m • a₀ < 0` from `a₀ < 0`, contradiction); conclude `div_neg_of_neg_of_pos`. Then
   `intro a b hab; have := key (b - a) (sub_pos.mpr hab); rw [map_sub] at this; linarith`.
2. `ratLog_unique`: `AddMonoidHom.ext fun a ↦ ?_`; `⟨m, n, hn, hmn⟩ := h a`; `have : n • g a = -m := by rw
   [← map_zsmul, hmn, map_zsmul, hg]; simp` (`zsmul_neg`, `smul_eq_mul`, `mul_one`... in `ℚ`, `n • q = n * q`:
   `zsmul_eq_mul`); then `rw [ratLog_eq ha₀ h hn hmn]`; `field_simp` / `eq_div_iff (by exact_mod_cast hn.ne')`
   from `this` (`linarith` after `zsmul_eq_mul`).
[SRC] `ratLog_strictMono`; the uniqueness is new (decomposition L2.6).
#### Mathlib lemmas needed
`zsmul_lt_zsmul_iff_left`, `lt_trichotomy`, `div_neg_of_neg_of_pos`, `sub_pos`, `map_sub`, `neg_pos`, `AddMonoidHom.ext`, `map_zsmul`, `zsmul_eq_mul`, `eq_div_iff`, `smul_eq_mul`.
#### Sources
[RM] §1.4.2 (Q2.1 'prove it strictly monotone'), §1.4.4 (Q4.4, whose substrate is L2.6); [Gou20] 3.1.3 (iv) (Q2.3) for the classical analogue; decomposition L2.5–L2.6. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T005; uniqueness among all `M →+ ℚ`, not only monotone ones.

### [CLEANUP-3] Run /cleanup on `RatLog.lean`
- **Status**: done (2026-10-06) · **File**: `RatLog.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T007] `Valuation.addVal`: `apply`, `eq_top`, `eq_coe`, order reversal
- **Status**: done (2026-10-06) · **File**: `Basic.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with T005, T006) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `addVal_apply` is `rfl`, `addVal_eq_coe`/`addVal_le_addVal` are term proofs (`negLog_eq_coe`, `negLog_le_negLog`). Lint: `@[simp]` dropped from `addVal_apply` (simpNF: it unfolds the definition and made `addVal_eq_top` simp-provable).
- **Leaves**: L1.14–L1.17

#### Statement
```lean
@[simp] lemma addVal_apply (v : Valuation R Mᵐ⁰) (x : R) : v.addVal x = negLog (v x) := by sorry
@[simp] lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by sorry
lemma addVal_eq_coe {v : Valuation R Mᵐ⁰} {x : R} {m : M} :
    v.addVal x = (m : WithTop M) ↔ v x = exp (-m) := by sorry
lemma addVal_le_addVal {v : Valuation R Mᵐ⁰} {x y : R} :
    v.addVal x ≤ v.addVal y ↔ v y ≤ v x := by sorry
```
#### Proof sketch
1. `addVal_apply`: `rfl` (`AddValuation.map_apply` and `Valuation.toAddValuation_apply` are `rfl`;
   `orderAddIsoWithTop M` applies as `negLog`).
2. `addVal_eq_top`: `rw [addVal_apply, WithZero.negLog_eq_top]` (or `simp`, as in [SRC]).
3. `addVal_eq_coe`: `rw [addVal_apply]; exact WithZero.negLog_eq_coe`.
4. `addVal_le_addVal`: `rw [addVal_apply, addVal_apply, WithZero.negLog_le_negLog]`.
[SRC] `AddVal/Basic.lean` `addVal_apply`, `addVal_eq_top`, `addVal_eq_coe`.
#### Mathlib lemmas needed
`AddValuation.map_apply`, `Valuation.toAddValuation_apply`.
#### Sources
[RM] §1.1.3 (Q1.3), [PR] #43580 (Q1.6); decomposition L1.14–L1.17. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[Ring R]`, `M` a linearly ordered additive group (as `addVal` itself).

### [T008] The tautological additive valuation `addValValueGroup`
- **Status**: done (2026-10-06) · **File**: `Basic.lean` · **Depends on**: T007 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `addValValueGroup_eq_top` crosses the `ValueGroup₀` ≟ `(Additive G)ᵐ⁰` seam by a term proof (`(negLog_eq_top (x := v.restrict x)).trans v.restrict_eq_zero_iff`); `rw` fails there (implicit-transparency type mismatch). `@[simp]` dropped from `addValValueGroup_apply` (simpNF).
- **Leaves**: L1.19, L1.20

#### Statement
```lean
@[simp] lemma addValValueGroup_apply (x : R) :
    v.addValValueGroup x = negLog (M := Additive (valueGroup (.ofClass v))) (v.restrict x) := by sorry
@[simp] lemma addValValueGroup_eq_top {x : R} : v.addValValueGroup x = ⊤ ↔ v x = 0 := by sorry
```
#### Proof sketch
1. `addValValueGroup_apply`: `rfl` (it is `addVal_apply` at `v.restrict`).
2. `addValValueGroup_eq_top`: `rw [addValValueGroup_apply, WithZero.negLog_eq_top, Valuation.restrict_eq_zero_iff]`.
[SRC] `addValValueGroup_apply`.
#### Mathlib lemmas needed
`Valuation.restrict_eq_zero_iff`, `Valuation.restrict`, `MonoidWithZeroHom.valueGroup`.
#### Sources
[RM] §1.1.4 (Q1.4), [PR] #43580 (Q1.6); decomposition L1.19–L1.20. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
Any `v : Valuation R Γ₀` over `[Ring R] [LinearOrderedCommGroupWithZero Γ₀]` — no rank hypothesis.

### [CLEANUP-ALL-1] Run /cleanup-all before milestone M1 (T009)
- **Status**: done (2026-10-06) · **Depends on**: T008, CLEANUP-2, CLEANUP-3 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: sweep done before the milestone: every finished module builds without warnings, `runLinter` clean, `#print axioms` standard on all declarations of the layer (`scratch/axioms.py`, 143 public declarations).
- Sweep before the milestone: `NegLog.lean`, `RatLog.lean`, `Basic.lean` (so far). Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T009] Naturality: `addVal_map` — the §1.1 dictionary is complete
- **Status**: done (2026-10-06) · **File**: `Basic.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorem · **Milestone**: M1 — `Valuation.addVal_map` with `addVal_eq_coe` is the dictionary of mathlib4#43578/#43580 ([RM] §1.1). `#print axioms` must be standard on `addVal_map`, `addVal_eq_coe`, `addVal_eq_top`.
- **Progress**: 2026-10-06 (session 18:50–19:25Z): one line, `negLog_mapAddHom' f (v x)`. M1 reached; std axioms (`scratch/axioms.py`).
- **Leaves**: L1.18

#### Statement
```lean
lemma addVal_map (v : Valuation R Mᵐ⁰) {f : M →+ N} (hf : StrictMono f) (x : R) :
    (v.map (mapAddHom' f) (mapAddHom'_strictMono hf).monotone).addVal x
      = WithTop.map f (v.addVal x) := by sorry
```
#### Proof sketch
1. `rw [addVal_apply, addVal_apply]`; the left side is `negLog ((v.map (mapAddHom' f) _) x)` and
   `Valuation.map_apply`/`rfl` turns it into `negLog (mapAddHom' f (v x))`.
2. `exact WithZero.negLog_mapAddHom' f (v x)`.
[SRC] `addVal_map` (one line: `negLog_expMap f (v x)`).
#### Mathlib lemmas needed
`Valuation.map`, `Valuation.map_apply`.
#### Sources
[RM] §1.1.4 (Q1.4 'Prove `Valuation.addVal_map`'), [PR] #43580 (Q1.6); decomposition L1.18. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`hf : StrictMono f` only to form the monotone argument of `Valuation.map` (the PR's shape).

### [CLEANUP-4] Run /cleanup on `Basic.lean`
- **Status**: done (2026-10-06) · **File**: `Basic.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T010] `RankOne.addVal`: apply, zero, `eq_top`, value `-log (hom (v x))`
- **Status**: done (2026-10-06) · **File**: `RankOne.lean` · **Depends on**: CLEANUP-4 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC]. `@[simp]` dropped from `RankOne.addVal_apply` and `RankOne.addVal_zero` (simpNF: unfolding lemma / instance of `AddValuation.map_zero`).
- **Leaves**: L3.1–L3.4

#### Statement
```lean
@[simp] lemma addVal_apply (x : R) :
    addVal v x = negLog (NNReal.toRealMultZero (RankOne.hom v (v.restrict x))) := by sorry
@[simp] lemma addVal_zero : addVal v 0 = ⊤ := by sorry
@[simp] lemma addVal_eq_top {x : R} : addVal v x = ⊤ ↔ v x = 0 := by sorry
lemma addVal_apply_of_val_ne_zero {x : R} (hx : v x ≠ 0) :
    addVal v x = ((-Real.log (RankOne.hom v (v.restrict x)) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `addVal_apply`: `rfl`.
2. `addVal_zero`: `AddValuation.map_zero _`.
3. `addVal_eq_top`: `rw [addVal, Valuation.addVal_eq_top]`; `show NNReal.toRealMultZero (RankOne.hom v (v.restrict
   x)) = 0 ↔ v x = 0`; `rw [map_eq_zero, RankOne.hom_eq_zero_iff, Valuation.restrict_eq_zero_iff]` — `map_eq_zero`
   needs `toRealMultZero` to be injective at `0` as a `MonoidWithZeroHom` with `[NoZeroDivisors]`-free statement:
   if `map_eq_zero` does not fire, prove `toRealMultZero y = 0 ↔ y = 0` directly by `split_ifs` and
   `WithZero.exp_ne_zero`.
4. `addVal_apply_of_val_ne_zero`: `have h : RankOne.hom v (v.restrict x) ≠ 0 := by rw [Ne, RankOne.hom_eq_zero_iff,
   Valuation.restrict_eq_zero_iff]; exact hx`; `rw [addVal_apply, NNReal.toRealMultZero_of_ne_zero h,
   WithZero.negLog_exp]`.
[SRC] `AddVal/RankOne.lean`, same names.
#### Mathlib lemmas needed
`Valuation.RankOne.hom`, `Valuation.RankOne.hom_eq_zero_iff`, `Valuation.restrict_eq_zero_iff`, `map_eq_zero`, `AddValuation.map_zero`.
#### Sources
[RM] §1.2.1 (Q3.1), [Kob84] III §3 (Q3.2); decomposition L3.1–L3.4. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[Ring R]`, any `[RankOne v]`.

### [T011] `RankOne.addVal` depends only on the real absolute value
- **Status**: done (2026-10-06) · **File**: `RankOne.lean` · **Depends on**: T010 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `AddValuation.ext fun x ↦ by rw [addVal_apply, addVal_apply, h x]`.
- **Leaves**: L3.5

#### Statement
```lean
lemma addVal_eq_of_hom_eq {w : Valuation R Γ₀} [RankOne w]
    (h : ∀ x, RankOne.hom v (v.restrict x) = RankOne.hom w (w.restrict x)) :
    addVal v = addVal w := by sorry
```
#### Proof sketch
1. `AddValuation.ext fun x ↦ ?_`; `rw [addVal_apply, addVal_apply, h x]`.
(New; [RM] §1.2.1's 'equivalent valuation with the matching hom' is exactly the hypothesis — `plan.md` D5.)
#### Mathlib lemmas needed
`AddValuation.ext`.
#### Sources
[RM] §1.2.1 (Q3.1, last clause); decomposition L3.5.
#### Generality decision
Two valuations `v w : Valuation R Γ₀` with arbitrary `RankOne` structures; the hypothesis compares `hom ∘ restrict` pointwise.

### [CLEANUP-5] Run /cleanup on `RankOne.lean`
- **Status**: done (2026-10-06) · **File**: `RankOne.lean` · **Depends on**: T011 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T012] `IsCommensurable`: basic consequences, the normalising element `commGen`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: CLEANUP-3, CLEANUP-5 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `of_forall_eq` via the structure (`(h π).symm ▸ …`, `simpa only [h]`); rest ported.
- **Leaves**: L4.1–L4.5

#### Statement
```lean
lemma IsCommensurable.val_ne_zero : v π ≠ 0 := by sorry
lemma IsCommensurable.of_forall_eq {w : Valuation R Γ₀} (h : ∀ x, w x = v x) :
    w.IsCommensurable π := by sorry
include π hπ in
lemma IsCommensurable.isNontrivial : v.IsNontrivial := by sorry
@[simp] lemma coe_commGen : ((commGen v π : Γ₀ˣ) : Γ₀) = v π := by sorry
lemma ofMul_commGen_neg : Additive.ofMul (commGen v π) < 0 := by sorry
```
#### Proof sketch
1. `val_ne_zero`: `hπ.val_pos.ne'`.
2. `of_forall_eq`: `exact ⟨by rw [h]; exact hπ.val_pos, by rw [h]; exact hπ.val_lt_one, fun x hx ↦ by
   simpa only [h] using hπ.exists_zpow_eq x (by rwa [h] at hx)⟩`.
3. `isNontrivial`: `⟨⟨π, hπ.val_pos.ne', hπ.val_lt_one.ne⟩⟩` (`Valuation.IsNontrivial` has the single field
   `exists_val_nontrivial : ∃ x, v x ≠ 0 ∧ v x ≠ 1`).
4. `coe_commGen`: `rfl`.
5. `ofMul_commGen_neg`: `show commGen v π < 1`; `rw [← Subtype.coe_lt_coe, ← Units.val_lt_val]`; `simpa using
   hπ.val_lt_one`.
[SRC] `AddVal/Commensurable.lean` (`val_ne_zero`, `coe_commGen`, `ofMul_commGen_neg`, `isNontrivial`).
#### Mathlib lemmas needed
`Valuation.IsNontrivial`, `Valuation.IsNontrivial.exists_val_nontrivial`, `Subtype.coe_lt_coe`, `Units.val_lt_val`, `Units.mk0`, `MonoidWithZeroHom.mem_valueGroup`.
#### Sources
[RM] §1.4.1 (Q4.1); decomposition L4.1–L4.5. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[Ring R]`; `of_forall_eq` for any two valuations into the same `Γ₀`.

### [T013] Every element of the value group is commensurable with `commGen`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported verbatim from [SRC] `exists_zpow_eq_commGen`.
- **Leaves**: L4.6

#### Statement
```lean
lemma isCommensurableWith_commGen (g : valueGroup (.ofClass v)) :
    AddCommGroup.IsCommensurableWith (Additive.ofMul (commGen v π)) (Additive.ofMul g) := by sorry
```
#### Proof sketch
1. `obtain ⟨a, ha, x, hax⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm (f := .ofClass v)).mp g.2`;
   `simp only [MonoidWithZeroHom.coe_ofClass] at ha hax` (`ha : v a ≠ 0`, `hax : v a * ↑↑g = v x`).
2. `hx : v x ≠ 0` from `hax` (`mul_ne_zero ha (Units.ne_zero _)`).
3. Witnesses `⟨m₁, n₁, hn₁, e₁⟩ := hπ.exists_zpow_eq x hx`, `⟨m₂, n₂, hn₂, e₂⟩ := hπ.exists_zpow_eq a ha`.
4. `refine ⟨m₁ * n₂ - m₂ * n₁, n₁ * n₂, mul_pos hn₁ hn₂, ?_⟩`; `show g ^ (n₁ * n₂) = commGen v π ^ (m₁ * n₂ - m₂ *
   n₁)`; `refine Subtype.ext (Units.ext ?_)`; `simp only [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val,
   coe_commGen]`; `hgx : ↑↑g = v x / v a` (from `hax`, `field_simp`); `rw [hgx, div_zpow, zpow_sub₀ (val_ne_zero v
   π), show v x ^ (n₁ * n₂) = v π ^ (m₁ * n₂) by rw [zpow_mul, e₁, ← zpow_mul], show v a ^ (n₁ * n₂) = v π ^ (m₂ *
   n₁) by rw [mul_comm n₁ n₂, zpow_mul, e₂, ← zpow_mul]]`.
[SRC] `exists_zpow_eq_commGen` (verbatim route).
#### Mathlib lemmas needed
`MonoidWithZeroHom.mem_valueGroup_iff_of_comm`, `MonoidWithZeroHom.coe_ofClass`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `Units.ne_zero`, `div_zpow`, `zpow_sub₀`, `zpow_mul`, `mul_pos`, `Subtype.ext`, `Units.ext`.
#### Sources
[RM] §1.4.1 (Q4.1) and the closure argument of decomposition R4 ([Gou20] 6.4.2, Q4.6); decomposition L4.6. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[Ring R]` (the value group is generated by the values; commutativity of `Γ₀` is what `mem_valueGroup_iff_of_comm` uses).

### [T014] `Valuation.ratLog`: strict monotonicity, normalisation, computation from a witness
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T013 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): three one-line wrappers of the `AddCommGroup.ratLog` API.
- **Leaves**: L4.7–L4.9

#### Statement
```lean
lemma ratLog_strictMono : StrictMono (ratLog v π) := by sorry
@[simp] lemma ratLog_commGen : ratLog v π (Additive.ofMul (commGen v π)) = -1 := by sorry
lemma ratLog_eq_of_zsmul {g : valueGroup (.ofClass v)} {m n : ℤ} (hn : 0 < n)
    (hmn : n • Additive.ofMul g = m • Additive.ofMul (commGen v π)) :
    ratLog v π (Additive.ofMul g) = -((m : ℚ) / (n : ℚ)) := by sorry
```
#### Proof sketch
1. `ratLog_strictMono`: `AddCommGroup.ratLog_strictMono _ _`.
2. `ratLog_commGen`: `AddCommGroup.ratLog_self _ _`.
3. `ratLog_eq_of_zsmul`: `AddCommGroup.ratLog_eq _ _ hn hmn`.
[SRC] same names.
#### Mathlib lemmas needed
(none beyond T005/T006.)
#### Sources
[RM] §1.4.2 (Q2.1); decomposition L4.7–L4.9. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T012.

### [CLEANUP-6] Run /cleanup on `Commensurable.lean`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T014 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T015] `addValQ`: apply, zero, `eq_top`, order reversal
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: CLEANUP-6 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `addValQ_eq_top` via `WithTop.map_eq_top_iff`; `addValQ_le_addValQ` via `WithTop.map_le_iff` then the term `(negLog_le_negLog (x := v.restrict x) …).trans v.restrict_le_iff` (seam). `@[simp]` dropped from `addValQ_apply`, `addValQ_zero` (simpNF).
- **Leaves**: L4.10–L4.12, L4.18

#### Statement
```lean
@[simp] lemma addValQ_apply (x : R) :
    v.addValQ π x = WithTop.map (ratLog v π) (v.addValValueGroup x) := by sorry
@[simp] lemma addValQ_zero : v.addValQ π 0 = ⊤ := by sorry
@[simp] lemma addValQ_eq_top {x : R} : v.addValQ π x = ⊤ ↔ v x = 0 := by sorry
lemma addValQ_le_addValQ {x y : R} : v.addValQ π x ≤ v.addValQ π y ↔ v y ≤ v x := by sorry
```
#### Proof sketch
1. `addValQ_apply`: `rfl` (`AddValuation.map_apply`; `AddMonoidHom.withTopMap` coerces to `WithTop.map`).
2. `addValQ_zero`: `AddValuation.map_zero _`.
3. `addValQ_eq_top`: `rw [addValQ_apply, WithTop.map_eq_top_iff, addValValueGroup_eq_top]`.
4. `addValQ_le_addValQ`: `rw [addValQ_apply, addValQ_apply, WithTop.map_le_iff _ (fun a b ↦
   (ratLog_strictMono v π).le_iff_le), addValValueGroup_apply, addValValueGroup_apply, WithZero.negLog_le_negLog,
   Valuation.restrict_le_iff]`.
[SRC] `addValQ_apply`, `addValQ_zero`; the other two are new API.
#### Mathlib lemmas needed
`AddValuation.map_apply`, `AddMonoidHom.withTopMap`, `WithTop.map_eq_top_iff`, `WithTop.map_le_iff`, `StrictMono.le_iff_le`, `Valuation.restrict_le_iff`.
#### Sources
[RM] §1.4.2 (Q4.2); decomposition L4.10–L4.12, L4.18. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T012.

### [T016] The workhorse `addValQ_eq_of_zpow` and its corollaries
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T015 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): workhorse ported ([SRC] private `addValValueGroup_of_coe` inlined as `hval`); `pow` form via `zpow_natCast` + `Int.cast_natCast`.
- **Leaves**: L4.13–L4.17

#### Statement
```lean
lemma addValQ_eq_of_zpow {x : R} {m n : ℤ} (hx : v x ≠ 0) (hn : 0 < n)
    (hmn : v x ^ n = v π ^ m) :
    v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry
lemma addValQ_eq_of_pow_eq_pow {x : R} {m n : ℕ} (hx : v x ≠ 0) (hn : 0 < n)
    (hmn : v x ^ n = v π ^ m) :
    v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry
@[simp] lemma addValQ_self : v.addValQ π π = 1 := by sorry
lemma addValQ_ne_top {x : R} (hx : v x ≠ 0) : v.addValQ π x ≠ ⊤ := by sorry
lemma exists_zpow_eq_and_addValQ {x : R} (hx : v x ≠ 0) :
    ∃ m n : ℤ, 0 < n ∧ v x ^ n = v π ^ m ∧
      v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry
```
#### Proof sketch
1. `addValQ_eq_of_zpow`: `hr : v.restrict x ≠ 0 := by simpa using hx`; `obtain ⟨g, hg⟩ : ∃ g : valueGroup
   (.ofClass v), v.restrict x = ↑g := ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩`; `hgx : ↑↑g = v x` from
   `v.embedding_restrict x` and `hg`; `hgn : n • Additive.ofMul g = m • Additive.ofMul (commGen v π)`: `show g ^ n
   = commGen v π ^ m; refine Subtype.ext (Units.ext ?_); simp only [SubgroupClass.coe_zpow,
   Units.val_zpow_eq_zpow_val, coe_commGen, hgx]; exact hmn`; then `rw [addValQ_apply, addValValueGroup_apply, hg]`
   (so the value is `WithTop.map ratLog ↑(-(ofMul g))`), `WithTop.map_coe, map_neg, ratLog_eq_of_zsmul v π hn hgn,
   neg_neg`. (In [SRC] the `addValValueGroup` step is the private `addValValueGroup_of_coe`; inline it or keep
   it as a private lemma.)
2. `addValQ_eq_of_pow_eq_pow`: `have := addValQ_eq_of_zpow v π hx (n := n) (m := m) (by exact_mod_cast hn) (by
   simpa only [zpow_natCast] using hmn)`; `simpa [Int.cast_natCast] using this`.
3. `addValQ_self`: `rw [addValQ_eq_of_zpow v π (IsCommensurable.val_ne_zero v π) one_pos rfl]; norm_num`
   (`v π ^ (1 : ℤ) = v π ^ (1 : ℤ)` is `rfl`).
4. `addValQ_ne_top`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; rw [addValQ_eq_of_zpow v π hx hn e]; exact
   WithTop.coe_ne_top`.
5. `exists_zpow_eq_and_addValQ`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; exact ⟨m, n, hn, e,
   addValQ_eq_of_zpow v π hx hn e⟩`.
[SRC] `addValQ_eq_of_zpow`, `addValQ_self`, `addValQ_ne_top`, `exists_zpow_eq_and_addValQ`.
#### Mathlib lemmas needed
`WithZero.unzero`, `WithZero.coe_unzero`, `Valuation.embedding_restrict`, `WithTop.map_coe`, `WithTop.coe_ne_top`, `map_neg`, `zpow_natCast`, `Int.cast_natCast`, `Nat.cast_pos`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`.
#### Sources
[RM] §1.4.3 (Q4.3), §1.4.2 (Q4.2 `addValQ v π π = 1`); decomposition L4.13–L4.17. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T012; the `pow` form is the one the normed examples use.

### [CLEANUP-ALL-2] Run /cleanup-all before milestone M2 (T017)
- **Status**: done (2026-10-06) · **Depends on**: T016, CLEANUP-5, CLEANUP-6 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: sweep done before the milestone: every finished module builds without warnings, `runLinter` clean, `#print axioms` standard on all declarations of the layer (`scratch/axioms.py`, 143 public declarations).
- Sweep before the milestone: `RankOne.lean`, `Commensurable.lean` (so far) and everything they import. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T017] Uniqueness: the element pins the valuation
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: theorem · **Milestone**: M2 — `Valuation.addValQ_unique` ([RM] §1.4.4, the justification of convention 3). `#print axioms` must be standard.
- **Progress**: 2026-10-06 (session 18:50–19:25Z): proved as planned: ⊤-case from the order hypothesis (`top_le_iff`, `map_zero`), finite case by comparing `x ^ c * π ^ b` with `π ^ a` (`m = a - b`, `n = c`), then `push_cast`/`eq_div_iff`/`linarith`. M2 reached; std axioms.
- **Leaves**: L4.19

#### Statement
```lean
theorem addValQ_unique (w : AddValuation R (WithTop ℚ))
    (hw : ∀ x y, w x ≤ w y ↔ v y ≤ v x)
    (hwπ : w π = 1) : w = v.addValQ π := by sorry
```
#### Proof sketch
1. `refine AddValuation.ext fun x ↦ ?_`. Lemma inside the proof: `hw_top : ∀ x, w x = ⊤ ↔ v x = 0`: `←`: from
   `v x ≤ v 0` (`v 0 = 0`, `Valuation.map_zero`) get `w 0 ≤ w x` by `(hw 0 x).mpr`, and `w 0 = ⊤`
   (`AddValuation.map_zero`), so `top_le_iff.mp`; `→`: `w 0 ≤ w x` holds, so `v x ≤ v 0 = 0`, i.e. `v x = 0`
   (`le_zero_iff`/`nonpos_iff_eq_zero` in `Γ₀`).
2. Case `hx : v x = 0`: `rw [(hw_top x).mpr hx, eq_comm, addValQ_eq_top]; exact hx`.
3. Case `v x ≠ 0`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx`. Set `a := m.toNat`, `b := (-m).toNat`; `hab :
   (a : ℤ) - b = m := Int.toNat_sub_toNat_neg m`; `hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm`.
   Compare the ring elements `y₁ := x ^ n.toNat * π ^ b` and `y₂ := π ^ a`: `hv : v y₁ = v y₂` by `map_mul, map_pow,
   ← zpow_natCast, ← hn', e, ← zpow_add₀ (val_ne_zero v π), hab`-style rewriting (both sides `v π ^ a`).
4. From `hv`, `(hw y₁ y₂).mpr hv.ge` and `(hw y₂ y₁).mpr hv.le` give `w y₁ = w y₂` (`le_antisymm`); rewrite with
   `AddValuation.map_mul, AddValuation.map_pow, hwπ`: `n.toNat • w x + b • (1 : WithTop ℚ) = a • 1`.
5. `w x ≠ ⊤` by `hw_top` and `hx`; `obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp this`; `rw [← hq] at *`;
   `norm_cast` / `WithTop.coe_inj` to get `(n.toNat : ℚ) * q + b = a` in `ℚ` (`nsmul_eq_mul`, `mul_one`);
   solve `q = (a - b) / n = m / n` (`eq_div_iff`, `linarith`, `push_cast [hab, hn']`).
6. `rw [← hq, addValQ_eq_of_zpow v π hx hn e]`; `congr 1`; the computed `q`.
Expect ~40 lines; the integer bookkeeping (`toNat`) is the only delicate part — keep `m` as `(a : ℤ) - b`
throughout.
#### Mathlib lemmas needed
`AddValuation.ext`, `AddValuation.map_zero`, `AddValuation.map_mul`, `AddValuation.map_pow`, `Valuation.map_zero`, `top_le_iff`, `le_antisymm`, `Int.toNat_sub_toNat_neg`, `Int.toNat_of_nonneg`, `zpow_natCast`, `zpow_add₀`, `map_mul`, `map_pow`, `WithTop.ne_top_iff_exists`, `WithTop.coe_inj`, `nsmul_eq_mul`, `eq_div_iff`.
#### Sources
[RM] §1.4.4 (Q4.4) and convention 3 (Q2.2); [Gou20] 3.1.3 (Q2.3) for the classical analogue; decomposition L4.19 (the prose proof is in R4).
#### Generality decision
`[Ring R]`; `w` an arbitrary `AddValuation R (WithTop ℚ)`; the order hypothesis is an `↔` for all pairs.

### [CLEANUP-7] Run /cleanup on `Commensurable.lean`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T017 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T018] Rational rank one implies rank one, with `hom (v π) = e⁻¹`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: CLEANUP-7 · **Parallel**: no · **Type**: def field + lemma
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `strictMono'` with `Rat.cast_lt` inline; `toRankOne_hom_restrict`: `v.restrict π = ↑(commGen v π)` by embedding injectivity, then `show` + `toNNReal_exp` + `simp [NNReal.rpow_neg_one]`.
- **Leaves**: L4.20, L4.21

#### Statement
```lean
noncomputable def IsCommensurable.toRankLeOne {e : ℝ≥0} (he : 1 < e) : RankLeOne v where
  hom' := (WithZeroMulReal.toNNReal (ne_zero_of_lt he)).comp
    (mapAddHom' (((Rat.castHom ℝ).toAddMonoidHom).comp (ratLog v π)))
  strictMono' := by sorry
lemma IsCommensurable.toRankOne_hom_restrict {e : ℝ≥0} (he : 1 < e) :
    letI := IsCommensurable.toRankOne v π he
    RankOne.hom v (v.restrict π) = e⁻¹ := by sorry
```
#### Proof sketch
1. `toRankLeOne.strictMono'`: `(WithZeroMulReal.toNNReal_strictMono he).comp (WithZero.mapAddHom'_strictMono
   (Rat.cast_strictMono.comp (ratLog_strictMono v π)))`.
2. `toRankOne_hom_restrict`: `letI := IsCommensurable.toRankOne v π he`; `show (WithZeroMulReal.toNNReal _).comp
   (WithZero.mapAddHom' _) (v.restrict π) = e⁻¹`; `hπ' : v.restrict π = WithZero.exp (Additive.ofMul (commGen v π))`
   by `MonoidWithZeroHom.ValueGroup₀.embedding_injective` + `Valuation.embedding_restrict` + `coe_commGen` (both
   sides embed to `v π`); `rw [MonoidWithZeroHom.comp_apply, hπ', WithZero.mapAddHom'_exp, AddMonoidHom.comp_apply,
   ratLog_commGen, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Rat.cast_neg, Rat.cast_one,
   WithZeroMulReal.toNNReal_exp, NNReal.rpow_neg_one]`.
[SRC] `toRankLeOne` (the hom and strictMono); the `hom = e⁻¹` lemma is new (it is the roadmap's clause).
#### Mathlib lemmas needed
`WithZeroMulReal.toNNReal_strictMono`, `WithZeroMulReal.toNNReal_exp`, `Rat.cast_strictMono`, `Rat.castHom`, `Rat.cast_neg`, `Rat.cast_one`, `NNReal.rpow_neg_one`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `MonoidWithZeroHom.comp_apply`, `AddMonoidHom.comp_apply`, `RingHom.toAddMonoidHom_eq_coe`, `AddMonoidHom.coe_coe`.
#### Sources
[RM] §1.4.5 (Q4.5, first sentence); decomposition L4.20–L4.21. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
Any base `1 < e`; the structure is `@[reducible]` so that `RankOne.hom v` unfolds.

### [T019] The compatibility square `ℚ → ℝ` and `‖x‖ = ‖π‖ ^ q`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T018 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC]; the ⊤ case now uses `addValQ_eq_top`.
- **Leaves**: L4.22, L4.23

#### Statement
```lean
theorem RankOne.addVal_eq_map_addValQ (x : R) :
    RankOne.addVal v x =
      WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log (RankOne.hom v (v.restrict π))))
        (v.addValQ π x) := by sorry
theorem RankOne.hom_eq_rpow_addValQ {x : R} {q : ℚ}
    (hq : v.addValQ π x = (q : WithTop ℚ)) :
    ((RankOne.hom v (v.restrict x) : ℝ)) = ((RankOne.hom v (v.restrict π) : ℝ)) ^ (q : ℝ) := by sorry
```
#### Proof sketch
1. `addVal_eq_map_addValQ`: `rcases eq_or_ne (v x) 0 with hx | hx`. Zero: `(addValQ_eq_top v π).mpr hx`,
   `WithTop.map_top`, `(RankOne.addVal_eq_top v).mpr hx`. Nonzero: `obtain ⟨m, n, hn, e, hq⟩ :=
   exists_zpow_eq_and_addValQ v π hx`; positivity of the two real hom values (`RankOne.hom_eq_zero_iff`,
   `Valuation.restrict_eq_zero_iff`, `NNReal.coe_pos`); `hres : v.restrict x ^ n = v.restrict π ^ m` via
   `MonoidWithZeroHom.ValueGroup₀.embedding_injective` and `map_zpow₀`, `Valuation.embedding_restrict`; apply `RankOne.hom
   v` (`map_zpow₀`), coerce to `ℝ` (`NNReal.coe_zpow`), take `Real.log` (`Real.log_zpow` twice); then `rw
   [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe, WithTop.coe_inj]; push_cast; field_simp;
   linarith`.
2. `hom_eq_rpow_addValQ`: `hx : v x ≠ 0` (else `addValQ = ⊤ ≠ ↑q`, by `addValQ_eq_top`); positivity as above;
   `h := addVal_eq_map_addValQ v π x`; `rw [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe,
   WithTop.coe_inj] at h`; `rw [Real.rpow_def_of_pos ht, ← Real.exp_log hs]; congr 1; linarith`.
[SRC] same names (verbatim route).
#### Mathlib lemmas needed
`Real.log_zpow`, `Real.rpow_def_of_pos`, `Real.exp_log`, `NNReal.coe_zpow`, `NNReal.coe_pos`, `map_zpow₀`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `Valuation.RankOne.hom_eq_zero_iff`, `WithTop.map_top`, `WithTop.map_coe`, `WithTop.coe_inj`.
#### Sources
[RM] §1.4.5 (Q4.5, 'the compatibility squares'), §1.4.6 (Q6.4, abstract form); [Gou20] 3.1.3 (iv) and p. 56 (Q2.3, Q4.7); decomposition L4.22–L4.23. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
Any `[RankOne v]` (not only `toRankOne`); `[Ring R]`.

### [CLEANUP-8] Run /cleanup on `Commensurable.lean`
- **Status**: done (2026-10-06) · **File**: `Commensurable.lean` · **Depends on**: T019 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T020] Discrete valuations: values are powers of the generator; commensurability at elements of valuation in `(0, 1)`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: CLEANUP-8 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `isCommensurable_of_lt_one` via `zpow_lt_one_iff_right_of_lt_one₀` in `Γ₀` on the coerced generator.
- **Leaves**: L5.1–L5.4

#### Statement
```lean
lemma IsRankOneDiscrete.exists_zpow_generator_eq {x : R} (hx : v x ≠ 0) :
    ∃ k : ℤ, v x = ((generator v ^ k : Γ₀ˣ) : Γ₀) := by sorry
lemma IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer {π : R} (hπ : IsUniformizer v π)
    {x : R} (hx : v x ≠ 0) : ∃ k : ℤ, v x = v π ^ k := by sorry
lemma IsRankOneDiscrete.isCommensurable_of_lt_one {π : R} (h0 : v π ≠ 0) (h1 : v π < 1) :
    v.IsCommensurable π := by sorry
lemma IsRankOneDiscrete.isCommensurable {π : R} (hπ : IsUniformizer v π) :
    v.IsCommensurable π := by sorry
```
#### Proof sketch
1. `exists_zpow_generator_eq`: `have hu : Units.mk0 (v x) hx ∈ valueGroup (.ofClass v) := mem_valueGroup _ ⟨x,
   rfl⟩`; `rw [← generator_zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hu`; `obtain ⟨k, hk⟩ := hu`;
   `exact ⟨k, by rw [← Units.val_mk0 hx, ← hk]⟩`.
2. `exists_zpow_eq_of_isUniformizer`: as [SRC]: `hπ.zpowers_eq_valueGroup`, `Subgroup.mem_zpowers_iff`, then
   `rw [← Units.val_mk0 hx, ← hk, Units.val_zpow_eq_zpow_val, Units.val_mk0]`.
3. `isCommensurable_of_lt_one`: `refine ⟨zero_lt_iff.mpr h0, h1, fun x hx ↦ ?_⟩`; `⟨k, hk⟩ :=
   exists_zpow_generator_eq v hx`, `⟨j, hj⟩ := exists_zpow_generator_eq v h0`; `hj0 : 0 < j`: from `h1 : v π < 1`
   rewritten by `hj` as `↑(generator v ^ j) < 1`, i.e. `generator v ^ j < 1` in `Γ₀ˣ` (`Units.val_lt_val`,
   `Units.val_one`), and `zpow_lt_one_iff_right_of_lt_one₀`-type lemma on the ordered group `Γ₀ˣ` (if the `₀`
   version does not apply to units, use `zpow_lt_one_iff_right_of_lt_one'`/`Left.zpow_lt_one_iff` — the
   ticket's name check lists `zpow_lt_one_iff_right_of_lt_one₀`; fall back to `zpow_strictAnti`-style lemmas
   `zpow_lt_zpow_iff_right_of_lt_one₀` with exponent `0`); witnesses `⟨k, j, hj0, by rw [hk, hj, ← Units.val_zpow_eq_zpow_val,
   ← Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_mul, mul_comm]⟩`.
4. `isCommensurable`: `isCommensurable_of_lt_one v hπ.val_ne_zero hπ.val_lt_one`.
[SRC] `exists_zpow_eq_of_isUniformizer`, `isCommensurable`.
#### Mathlib lemmas needed
`MonoidWithZeroHom.mem_valueGroup`, `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`, `Valuation.IsUniformizer.zpowers_eq_valueGroup`, `Valuation.IsUniformizer.val_ne_zero`, `Valuation.IsUniformizer.val_lt_one`, `Subgroup.mem_zpowers_iff`, `Units.val_mk0`, `Units.val_zpow_eq_zpow_val`, `Units.val_lt_val`, `Units.val_one`, `zpow_lt_one_iff_right_of_lt_one₀`, `zpow_mul`, `zero_lt_iff`, `mul_comm`.
#### Sources
[RM] §1.4.1 (Q4.1, 'IsRankOneDiscrete implies IsCommensurable at every uniformiser'), §1.3.1 (Q5.1); [Kob84] III §3 (Q5.4), [Gou20] 6.4.5 (Q5.5); decomposition L5.1–L5.4. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`[Ring R]`, any discrete `v`; L5.3 is stated at any element with `0 < v π < 1` (more general than the roadmap's uniformiser).

### [T021] `addValZ`: apply, zero, `eq_top`, order reversal
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `addValZ_eq_top` by `map_eq_zero` through the `≃*o`; `@[simp]` dropped from `addValZ_apply`, `addValZ_zero` (simpNF).
- **Leaves**: L5.5–L5.7, L5.12

#### Statement
```lean
@[simp] lemma IsRankOneDiscrete.addValZ_apply (x : R) :
    addValZ v x = negLog (valueGroup₀_equiv_withZeroMulInt v (v.restrict x)) := by sorry
@[simp] lemma IsRankOneDiscrete.addValZ_zero : addValZ v 0 = ⊤ := by sorry
@[simp] lemma IsRankOneDiscrete.addValZ_eq_top {x : R} : addValZ v x = ⊤ ↔ v x = 0 := by sorry
lemma IsRankOneDiscrete.addValZ_le_addValZ {x y : R} :
    addValZ v x ≤ addValZ v y ↔ v y ≤ v x := by sorry
```
#### Proof sketch
1. `addValZ_apply`: `rfl`.
2. `addValZ_zero`: `AddValuation.map_zero _`.
3. `addValZ_eq_top`: `rw [addValZ_apply, WithZero.negLog_eq_top, map_eq_zero, Valuation.restrict_eq_zero_iff]`
   (`map_eq_zero` through `MonoidWithZeroHom.coe_ofClass`/the `MulEquivClass` instance of `≃*o`; if it does not
   fire, use `(valueGroup₀_equiv_withZeroMulInt v).map_eq_zero_iff`).
4. `addValZ_le_addValZ`: `rw [addValZ_apply, addValZ_apply, WithZero.negLog_le_negLog,
   (valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le, Valuation.restrict_le_iff]`.
[SRC] `addValZ_apply`, `addValZ_zero`.
#### Mathlib lemmas needed
`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt`, `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono`, `map_eq_zero`, `MonoidWithZeroHom.coe_ofClass`, `Valuation.restrict_eq_zero_iff`, `Valuation.restrict_le_iff`, `StrictMono.le_iff_le`.
#### Sources
[RM] §1.3.1 (Q5.1); decomposition L5.5–L5.7, L5.12. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T020.

### [T022] The characterisation `addValZ v x = k ↔ v x = generator ^ k`, at a uniformiser, and `addValZ π = 1`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: T021 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `addValZ_eq_iff` by one `rw` chain (`negLog_eq_coe`, `← …_apply_zpow v k`, `EquivLike.injective`, embedding injectivity, `embedding_generator'`); the other three are corollaries.
- **Leaves**: L5.8–L5.11

#### Statement
```lean
theorem IsRankOneDiscrete.addValZ_eq_iff (x : R) (k : ℤ) :
    addValZ v x = (k : WithTop ℤ) ↔ v x = ((generator v ^ k : Γ₀ˣ) : Γ₀) := by sorry
lemma IsRankOneDiscrete.addValZ_eq_of_zpow {π : R} (hπ : IsUniformizer v π) {x : R} {k : ℤ}
    (hk : v x = v π ^ k) : addValZ v x = (k : WithTop ℤ) := by sorry
theorem IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer {π : R} (hπ : IsUniformizer v π)
    (x : R) (k : ℤ) : addValZ v x = (k : WithTop ℤ) ↔ v x = v π ^ k := by sorry
theorem IsRankOneDiscrete.addValZ_isUniformizer {π : R} (hπ : IsUniformizer v π) :
    addValZ v π = 1 := by sorry
```
#### Proof sketch
1. `addValZ_eq_iff`: `rw [addValZ_apply, WithZero.negLog_eq_coe]`; `h1 : v.restrict x = generator' v ^ k ↔
   valueGroup₀_equiv_withZeroMulInt v (v.restrict x) = WithZero.exp (-k)` by `(valueGroup₀_equiv_withZeroMulInt
   v).injective.eq_iff` and `valueGroup₀_equiv_withZeroMulInt_apply_zpow`; `h2 : v.restrict x = generator' v ^ k ↔ v
   x = ↑(generator v ^ k)` by `MonoidWithZeroHom.ValueGroup₀.embedding_injective.eq_iff`, `map_zpow₀`,
   `embedding_generator'`, `Valuation.embedding_restrict`, `Units.val_zpow_eq_zpow_val`; `exact h1.symm.trans h2`.
2. `addValZ_eq_of_zpow`: [SRC] verbatim: `h1 : v.restrict x = v.restrict π ^ k` and `h2 : v.restrict π = ↑(generator'
   v)` by embedding injectivity (`map_zpow₀`, `embedding_restrict`, `hπ`), then `rw [addValZ_apply, negLog_eq_coe,
   h1, h2, valueGroup₀_equiv_withZeroMulInt_apply_zpow]`.
3. `addValZ_eq_iff_of_isUniformizer`: `rw [addValZ_eq_iff, hπ.val, ← Units.val_zpow_eq_zpow_val]`.
4. `addValZ_isUniformizer`: `have := addValZ_eq_of_zpow v hπ (x := π) (k := 1) (zpow_one _).symm; simpa using this`
   (`WithTop.coe_one`).
[SRC] `addValZ_eq_of_zpow`.
#### Mathlib lemmas needed
`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow`, `Valuation.IsRankOneDiscrete.embedding_generator'`, `Valuation.IsRankOneDiscrete.generator'`, `Valuation.IsUniformizer.val`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `map_zpow₀`, `Units.val_zpow_eq_zpow_val`, `zpow_one`, `WithTop.coe_one`, `MulEquiv.injective`.
#### Sources
[RM] §1.3.1 (Q5.1), §1.3.2 (Q5.2); [Kob84] III §3 (Q5.4), [Gou20] 6.4.5 (Q5.5), Mathlib docstring (Q5.7); decomposition L5.8–L5.11. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T020.

### [CLEANUP-9] Run /cleanup on `Discrete.lean`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: T022 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T023] `addValQ` at a uniformiser is `addValZ` composed with `Int.cast`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: CLEANUP-9 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC].
- **Leaves**: L5.13

#### Statement
```lean
theorem addValQ_eq_map_addValZ {π : R} (hπ : IsUniformizer v π) [v.IsCommensurable π] (x : R) :
    v.addValQ π x = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (addValZ v x) := by sorry
```
#### Proof sketch
1. `rcases eq_or_ne (v x) 0 with hx | hx`. Zero: `(addValQ_eq_top v π).mpr hx`, `(addValZ_eq_top v).mpr hx`,
   `WithTop.map_top`.
2. Nonzero: `obtain ⟨k, hk⟩ := exists_zpow_eq_of_isUniformizer v hπ hx`; `rw [addValQ_eq_of_zpow v π hx one_pos
   (by rw [zpow_one, hk]), addValZ_eq_of_zpow v hπ hk, WithTop.map_coe]; norm_num`.
[SRC] `addValQ_eq_map_addValZ` (verbatim).
#### Mathlib lemmas needed
`WithTop.map_top`, `WithTop.map_coe`, `zpow_one`.
#### Sources
[RM] §1.4.5 (Q4.5, last clause); decomposition L5.13. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
As T020; the `IsCommensurable` instance is a hypothesis (derivable by T020) so the statement is usable with any instance.

### [T024] Norm recovery on a discrete valuation: `hom` is determined by the generator; `hom (v x) = e ^ (-d)`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: T023 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC] (private `toNNReal_exp` for `WithZeroMulInt.toNNReal (exp n) = e ^ n`); uniformiser form via `v.restrict π = ↑(generator' v)`.
- **Leaves**: L5.14–L5.16

#### Statement
```lean
lemma IsRankOneDiscrete.hom_eq_toNNReal_comp [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ (.ofClass v)) = e⁻¹) :
    RankOne.hom v =
      (WithZeroMulInt.toNNReal he).comp (.ofClass (valueGroup₀_equiv_withZeroMulInt v)) := by sorry
theorem IsRankOneDiscrete.hom_eq_zpow_neg_addValZ [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ (.ofClass v)) = e⁻¹)
    {x : R} {d : ℤ} (hd : addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by sorry
theorem IsRankOneDiscrete.hom_eq_zpow_neg_addValZ_of_isUniformizer [RankOne v] {π : R}
    (hπ : IsUniformizer v π) {e : ℝ≥0} (he : e ≠ 0)
    (hπe : RankOne.hom v (v.restrict π) = e⁻¹)
    {x : R} {d : ℤ} (hd : addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by sorry
```
#### Proof sketch
1. `hom_eq_toNNReal_comp`: `refine MonoidWithZeroHom.ext fun γ ↦ ?_`; `induction γ using WithZero.recZeroCoe with
   | zero => simp | coe u => ?_`; `obtain ⟨k, rfl⟩ : ∃ k : ℤ, generator' v ^ k = u := Subgroup.mem_zpowers_iff.mp (by
   rw [generator'_zpowers_eq_top]; exact Subgroup.mem_top u)`; `rw [MonoidWithZeroHom.comp_apply,
   MonoidWithZeroHom.coe_ofClass, WithZero.coe_zpow, valueGroup₀_equiv_withZeroMulInt_apply_zpow,
   WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, map_zpow₀, hgen, inv_zpow, ← zpow_neg]` and the
   `toAdd (unzero (exp (-k))) = -k` simp fact.
2. `hom_eq_zpow_neg_addValZ`: `rw [addValZ_apply, WithZero.negLog_eq_coe] at hd`; `rw [hom_eq_toNNReal_comp v he hgen,
   MonoidWithZeroHom.comp_apply, MonoidWithZeroHom.coe_ofClass, hd, WithZeroMulInt.toNNReal_neg_apply he
   WithZero.exp_ne_zero]`; finish the `toAdd (unzero _)` computation with `simp`.
3. `hom_eq_zpow_neg_addValZ_of_isUniformizer`: `h : v.restrict π = ↑(generator' v)` (embedding injectivity + `hπ`);
   `exact hom_eq_zpow_neg_addValZ v he (by rwa [← h]) hd`.
[SRC] `hb_of_norm_generator`, `hom_eq_zpow_neg_addValZ` (the private `toNNReal_exp` helper there is
`WithZeroMulInt.toNNReal_neg_apply` plus `WithZero.log_exp`).
#### Mathlib lemmas needed
`MonoidWithZeroHom.ext`, `WithZero.recZeroCoe`, `Valuation.IsRankOneDiscrete.generator'_zpowers_eq_top`, `Subgroup.mem_zpowers_iff`, `Subgroup.mem_top`, `MonoidWithZeroHom.comp_apply`, `MonoidWithZeroHom.coe_ofClass`, `WithZero.coe_zpow`, `WithZeroMulInt.toNNReal_neg_apply`, `WithZero.exp_ne_zero`, `map_zpow₀`, `inv_zpow`, `zpow_neg`, `WithZero.unzero`.
#### Sources
[RM] §1.3.3 (Q5.3); [Kob84] I §2 (Q5.6); decomposition L5.14–L5.16. [SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`), never `import PhD.Main.*`.
#### Generality decision
`he : e ≠ 0` only (the roadmap's `e > 1` is not needed); any `[RankOne v]`.

### [CLEANUP-10] Run /cleanup on `Discrete.lean`
- **Status**: done (2026-10-06) · **File**: `Discrete.lean` · **Depends on**: T024 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T025] The norm of a normed field is the rank-one `hom` of `NormedField.valuation`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: CLEANUP-10 · **Parallel**: yes (with T036–T038) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC] `Valued/AddVal.lean`.
- **Leaves**: L6.1–L6.3

#### Statement
```lean
lemma addVal_apply_of_ne_zero {x : L} (hx : x ≠ 0) :
    addVal v x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by sorry
@[simp] lemma valuation_norm_eq (x : K) : (valuation (K := K)).norm x = ‖x‖ := by sorry
lemma norm_eq_coe_hom (x : K) :
    ‖x‖ = ((RankOne.hom (valuation (K := K)) ((valuation (K := K)).restrict x) : ℝ≥0) : ℝ) := by sorry
```
#### Proof sketch
1. `Valuation.RankOne.addVal_apply_of_ne_zero` (field): `h : RankOne.hom v (v.restrict x) ≠ 0` by `rw [Ne,
   RankOne.hom_eq_zero_iff, v.restrict_eq_zero_iff, v.zero_iff]; exact hx`; `rw [addVal_apply,
   NNReal.toRealMultZero_of_ne_zero h, WithZero.negLog_exp]; rfl` (`Valuation.norm_def`).
2. `valuation_norm_eq`: `rw [Valuation.norm_def, Valuation.restrict_def]`; `show ((embedding (restrict₀ (.ofClass
   (valuation (K := K))) x) : ℝ≥0) : ℝ) = ‖x‖` (the `RankOne` instance's `hom'` is `ValueGroup₀.embedding`);
   `rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]; rfl` (`valuation_apply`, `coe_nnnorm`).
3. `norm_eq_coe_hom`: `rw [← valuation_norm_eq K x]; rfl`.
[SRC] `Valued/AddVal.lean` `addVal_apply_of_ne_zero`, `valuation_norm_eq`, `norm_eq_coe_hom`.
#### Mathlib lemmas needed
`Valuation.norm_def`, `Valuation.restrict_def`, `Valuation.zero_iff`, `MonoidWithZeroHom.ValueGroup₀.embedding`, `MonoidWithZeroHom.ValueGroup₀.restrict₀`, `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`, `NormedField.valuation_apply`, `coe_nnnorm`.
#### Sources
[RM] §1.2.2 (Q6.1), Mathlib's `NormedField.valuation` and its `RankOne` instance (Q6.6); decomposition L6.1–L6.3. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`[NontriviallyNormedField K] [IsUltrametricDist K]` (the `RankOne` instance needs nontriviality); L6.1 for any rank-one valuation on a field.

### [T026] `normAddVal`: zero, `eq_top`, `-log ‖x‖`, the defining equivalence, order reversal
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T025 · **Parallel**: yes (with T036–T038) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): order reversal by cases on zero and `Real.log_le_log_iff`. `@[simp]` dropped from `normAddVal_zero`, `normAddVal_eq_top` (simp proves them by `AddValuation.map_zero`/`top_iff`).
- **Leaves**: L6.4–L6.8

#### Statement
```lean
@[simp] lemma normAddVal_zero : normAddVal K 0 = ⊤ := by sorry
@[simp] lemma normAddVal_eq_top {x : K} : normAddVal K x = ⊤ ↔ x = 0 := by sorry
lemma normAddVal_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    normAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by sorry
lemma exists_normAddVal_eq_and_norm_eq_exp_neg {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, normAddVal K x = (r : WithTop ℝ) ∧ ‖x‖ = Real.exp (-r) := by sorry
lemma normAddVal_le_normAddVal {x y : K} :
    normAddVal K x ≤ normAddVal K y ↔ ‖y‖ ≤ ‖x‖ := by sorry
```
#### Proof sketch
1. `normAddVal_zero`: `AddValuation.map_zero _`.
2. `normAddVal_eq_top`: `rw [normAddVal, RankOne.addVal_eq_top, Valuation.zero_iff]`.
3. `normAddVal_apply_of_ne_zero`: `rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]`.
4. `exists_normAddVal_eq_and_norm_eq_exp_neg`: `refine ⟨-Real.log ‖x‖, normAddVal_apply_of_ne_zero K hx, ?_⟩; rw
   [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]`.
5. `normAddVal_le_normAddVal`: `show (RankOne.realValuation _).addVal x ≤ _ ↔ _`; `rw [Valuation.addVal_le_addVal]`;
   `RankOne.realValuation v y ≤ RankOne.realValuation v x ↔ v y ≤ v x` is `(NNReal.toRealMultZero_strictMono.comp
   (RankOne.strictMono _)).le_iff_le` after unfolding `Valuation.map` (`rfl`); then `Valuation.restrict_le_iff`,
   `valuation_apply`, `NNReal.coe_le_coe`, `coe_nnnorm`.
[SRC] `normAddVal_zero`, `normAddVal_apply_of_ne_zero`.
#### Mathlib lemmas needed
`AddValuation.map_zero`, `Valuation.zero_iff`, `Real.exp_log`, `norm_pos_iff`, `neg_neg`, `StrictMono.le_iff_le`, `Valuation.restrict_le_iff`, `NNReal.coe_le_coe`, `coe_nnnorm`, `Valuation.RankOne.strictMono`.
#### Sources
[RM] §1.2.2 (Q6.1), §1.2.3 (Q6.2, 'the defining equivalence'); [Kob84] III §4 (Q6.5); decomposition L6.4–L6.8. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
As T025.

### [T027] `normAddVal` is the unique additive valuation with `‖x‖ = exp (-(v x))`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T026 · **Parallel**: yes (with T036–T038) · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `r = -log ‖x‖` from `‖x‖ = exp (-r)` by `Real.log_exp`.
- **Leaves**: L6.9

#### Statement
```lean
theorem normAddVal_unique (w : AddValuation K (WithTop ℝ))
    (hw : ∀ x : K, x ≠ 0 → ∃ r : ℝ, w x = (r : WithTop ℝ) ∧ ‖x‖ = Real.exp (-r)) :
    w = normAddVal K := by sorry
```
#### Proof sketch
1. `refine AddValuation.ext fun x ↦ ?_`; `rcases eq_or_ne x 0 with rfl | hx`.
2. Zero: `rw [AddValuation.map_zero, normAddVal_zero]`.
3. Nonzero: `obtain ⟨r, hr, hxr⟩ := hw x hx`; `hr' : r = -Real.log ‖x‖ := by have := congrArg Real.log hxr; rw
   [Real.log_exp] at this; linarith`; `rw [hr, hr', normAddVal_apply_of_ne_zero K hx]`.
(New: decomposition L6.9.)
#### Mathlib lemmas needed
`AddValuation.ext`, `AddValuation.map_zero`, `Real.log_exp`.
#### Sources
[RM] §1.2.3 (Q6.2, 'the unique additive valuation into `WithTop ℝ` satisfying it'); decomposition L6.9.
#### Generality decision
As T025; `w` arbitrary.

### [CLEANUP-11] Run /cleanup on `Normed.lean`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T027 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T028] `normAddValZ`: zero, `eq_top`, the characterisation `‖x‖ = ‖π‖ ^ k`, `normAddValZ π = 1`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: CLEANUP-11 · **Parallel**: yes (with T036–T038) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): characterisation through `valuation_apply`, `NNReal.coe_inj`, `NNReal.coe_zpow`. `@[simp]` dropped from `normAddValZ_zero`, `normAddValZ_eq_top` (simpNF).
- **Leaves**: L6.10–L6.13

#### Statement
```lean
@[simp] lemma normAddValZ_zero : normAddValZ K 0 = ⊤ := by sorry
@[simp] lemma normAddValZ_eq_top {x : K} : normAddValZ K x = ⊤ ↔ x = 0 := by sorry
theorem normAddValZ_eq_iff_of_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π)
    (x : K) (k : ℤ) : normAddValZ K x = (k : WithTop ℤ) ↔ ‖x‖ = ‖π‖ ^ k := by sorry
theorem normAddValZ_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    normAddValZ K π = 1 := by sorry
```
#### Proof sketch
1. `normAddValZ_zero`: `AddValuation.map_zero _`.
2. `normAddValZ_eq_top`: `rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_top, Valuation.zero_iff]`.
3. `normAddValZ_eq_iff_of_isUniformizer`: `rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer _ hπ,
   valuation_apply, valuation_apply, ← NNReal.coe_inj, NNReal.coe_zpow, coe_nnnorm, coe_nnnorm]`.
4. `normAddValZ_isUniformizer`: `IsRankOneDiscrete.addValZ_isUniformizer _ hπ`.
[SRC] `normAddValZ_zero`.
#### Mathlib lemmas needed
`Valuation.zero_iff`, `NormedField.valuation_apply`, `NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`.
#### Sources
[RM] §1.3.4 (Q6.3), §1.3.2 (Q5.2) read through the norm; [Kob84] III §3 (Q5.4); decomposition L6.10–L6.13. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`[(valuation (K := K)).IsRankOneDiscrete]` as an instance hypothesis, to be supplied by `Padic.lean` (and by any discretely valued normed field).

### [T029] Norm recovery in the discrete case and the square `ℤ → ℝ`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T028 · **Parallel**: yes (with T036–T038) · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): uniformiser form by `inv_zpow'`; the `ℤ → ℝ` square by `Real.log_zpow` and `ring`.
- **Leaves**: L6.14–L6.16

#### Statement
```lean
theorem norm_eq_zpow_neg_normAddValZ {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom (valuation (K := K))
      (IsRankOneDiscrete.generator' (valuation (K := K)) :
        ValueGroup₀ (.ofClass (valuation (K := K)))) = e⁻¹)
    {x : K} {d : ℤ} (hd : normAddValZ K x = (d : WithTop ℤ)) :
    ‖x‖ = (e : ℝ) ^ (-d) := by sorry
theorem norm_eq_zpow_neg_normAddValZ_of_isUniformizer {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) {e : ℝ} (hπe : ‖π‖ = e⁻¹)
    {x : K} {d : ℤ} (hd : normAddValZ K x = (d : WithTop ℤ)) : ‖x‖ = e ^ (-d) := by sorry
theorem normAddVal_eq_map_normAddValZ {π : K} (hπ : IsUniformizer (valuation (K := K)) π)
    (x : K) :
    normAddVal K x
      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * (-Real.log ‖π‖)) (normAddValZ K x) := by sorry
```
#### Proof sketch
1. `norm_eq_zpow_neg_normAddValZ`: `rw [norm_eq_coe_hom K x, IsRankOneDiscrete.hom_eq_zpow_neg_addValZ _ he hgen
   hd, NNReal.coe_zpow]` ([SRC] verbatim).
2. `norm_eq_zpow_neg_normAddValZ_of_isUniformizer`: `rw [(normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd, hπe,
   inv_zpow', zpow_neg]` (check the direction of `inv_zpow'`: `a⁻¹ ^ n = a ^ (-n)`).
3. `normAddVal_eq_map_normAddValZ`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `normAddVal_zero, normAddValZ_zero,
   WithTop.map_top`); `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)`; `rw [←
   hd, WithTop.map_coe, normAddVal_apply_of_ne_zero K hx, (normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd.symm,
   Real.log_zpow]; congr 1; ring`.
[SRC] `norm_eq_zpow_neg_normAddValZ`; the other two are new.
#### Mathlib lemmas needed
`NNReal.coe_zpow`, `inv_zpow'`, `zpow_neg`, `WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `Real.log_zpow`.
#### Sources
[RM] §1.3.4 (Q6.3), §1.3.3 (Q5.3), §1.4.5 (Q4.5 pattern); [Kob84] I §2 (Q5.6); [Gou20] p. 56 (Q4.7); decomposition L6.14–L6.16. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`e : ℝ≥0`, `e ≠ 0` for the generator form; `e : ℝ` pinned by `‖π‖ = e⁻¹` for the uniformiser form (no positivity hypothesis).

### [T030] `normAddValQ`: zero, `eq_top`, `normAddValQ π = 1`, the workhorse read off norms
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T029 · **Parallel**: yes (with T036–T038) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `@[simp]` dropped from `normAddValQ_zero`, `normAddValQ_eq_top` (simpNF).
- **Leaves**: L6.17–L6.20

#### Statement
```lean
@[simp] lemma normAddValQ_zero : normAddValQ K π 0 = ⊤ := by sorry
@[simp] lemma normAddValQ_eq_top {x : K} : normAddValQ K π x = ⊤ ↔ x = 0 := by sorry
@[simp] lemma normAddValQ_self : normAddValQ K π π = 1 := by sorry
lemma normAddValQ_eq_of_pow_eq_pow {x : K} (hx : x ≠ 0) {m n : ℕ} (hn : 0 < n)
    (h : ‖x‖ ^ n = ‖π‖ ^ m) :
    normAddValQ K π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by sorry
```
#### Proof sketch
1. `normAddValQ_zero`: `AddValuation.map_zero _`.
2. `normAddValQ_eq_top`: `rw [normAddValQ, addValQ_eq_top, Valuation.zero_iff]`.
3. `normAddValQ_self`: `Valuation.addValQ_self _ _`.
4. `normAddValQ_eq_of_pow_eq_pow`: `refine addValQ_eq_of_pow_eq_pow _ π ((Valuation.ne_zero_iff _).mpr hx) hn ?_`;
   `rw [valuation_apply, valuation_apply, ← NNReal.coe_inj]; push_cast; exact h` (`NNReal.coe_pow`, `coe_nnnorm`).
[SRC] `normAddValQ_zero`, `normAddValQ_self`.
#### Mathlib lemmas needed
`Valuation.zero_iff`, `Valuation.ne_zero_iff`, `NormedField.valuation_apply`, `NNReal.coe_inj`, `NNReal.coe_pow`, `coe_nnnorm`.
#### Sources
[RM] §1.4.6 (Q6.4), §1.4.2–§1.4.3 (Q4.2, Q4.3); decomposition L6.17–L6.20. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`[(valuation (K := K)).IsCommensurable π]` as an instance hypothesis.

### [CLEANUP-12] Run /cleanup on `Normed.lean`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T030 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [T031] `‖x‖ = ‖π‖ ^ q`, and the squares `ℚ → ℝ`, `ℤ → ℚ` read off the norm
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: CLEANUP-12 · **Parallel**: yes (with T036–T038) · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `normAddVal_eq_map_normAddValQ` by `rwa [← norm_eq_coe_hom K π]` inside the lambda.
- **Leaves**: L6.21–L6.23

#### Statement
```lean
theorem norm_eq_norm_rpow_normAddValQ {x : K} {q : ℚ}
    (hq : normAddValQ K π x = (q : WithTop ℚ)) :
    ‖x‖ = ‖π‖ ^ (q : ℝ) := by sorry
theorem normAddVal_eq_map_normAddValQ (x : K) :
    normAddVal K x
      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log ‖π‖)) (normAddValQ K π x) := by sorry
theorem normAddValQ_eq_map_normAddValZ [(valuation (K := K)).IsRankOneDiscrete]
    (hπ : IsUniformizer (valuation (K := K)) π) (x : K) :
    normAddValQ K π x = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (normAddValZ K x) := by sorry
```
#### Proof sketch
1. `norm_eq_norm_rpow_normAddValQ`: `rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]; exact
   Valuation.RankOne.hom_eq_rpow_addValQ _ π hq` ([SRC] verbatim).
2. `normAddVal_eq_map_normAddValQ`: `have := Valuation.RankOne.addVal_eq_map_addValQ (valuation (K := K)) π x`; `rwa
   [← norm_eq_coe_hom K π] at this` (unfold `normAddVal`, `normAddValQ`).
3. `normAddValQ_eq_map_normAddValZ`: `Valuation.addValQ_eq_map_addValZ _ hπ x`.
[SRC] `norm_eq_norm_rpow_normAddValQ`.
#### Mathlib lemmas needed
(none beyond T019, T023, T025.)
#### Sources
[RM] §1.4.6 (Q6.4), §1.4.5 (Q4.5); decomposition L6.21–L6.23. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
As T030; the `ℤ → ℚ` square additionally assumes discreteness and a uniformiser.

### [CLEANUP-13] Run /cleanup on `Normed.lean`
- **Status**: done (2026-10-06) · **File**: `Normed.lean` · **Depends on**: T031 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T032] `ℚ_p`: the norm of `p`, and the value group is generated by `‖p‖₊`
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: CLEANUP-13 · **Parallel**: yes (with T039–T044) · **Type**: lemmas
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC] `Padics/AddVal.lean` (`padicGen` → `valueGroupGen`).
- **Leaves**: L7.1–L7.4

#### Statement
```lean
lemma nnnorm_p_eq_inv : ‖(p : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by sorry
lemma nnnorm_p_ne_zero : ‖(p : ℚ_[p])‖₊ ≠ 0 := by sorry
lemma nnnorm_p_zpow_valuation {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖(p : ℚ_[p])‖₊ ^ x.valuation = ‖x‖₊ := by sorry
lemma zpowers_valueGroupGen : Subgroup.zpowers (valueGroupGen (p := p)) = ⊤ := by sorry
```
#### Proof sketch
1. `nnnorm_p_eq_inv`: `rw [← NNReal.coe_inj]; push_cast; exact Padic.norm_p`.
2. `nnnorm_p_ne_zero`: `rw [nnnorm_p_eq_inv]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`.
3. `nnnorm_p_zpow_valuation`: `rw [← NNReal.coe_inj]; push_cast; rw [Padic.norm_eq_zpow_neg_valuation hx,
   Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), Padic.valuation_p, ←
   zpow_mul]; ring_nf` ([SRC] `padic_norm_zpow_valuation`).
4. `zpowers_valueGroupGen`: `rw [Subgroup.eq_top_iff']; intro y; rw [Subgroup.mem_zpowers_iff]`; `hy : (y : ℝ≥0ˣ).val
   ∈ Units.val '' valueGroup _ := ⟨y, y.2, rfl⟩`; `rw [MonoidWithZeroHom.valueGroup_eq_range] at hy`; `obtain ⟨⟨x,
   hx⟩, hne⟩ := hy`; `hx0 : x ≠ 0` (else `‖0‖₊ = 0`, contradicting `hne`); `refine ⟨x.valuation, Subtype.ext
   (Units.ext ?_)⟩`; `rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, show ((valueGroupGen (p := p)) :
   ℝ≥0ˣ).val = ‖(p : ℚ_[p])‖₊ from rfl, nnnorm_p_zpow_valuation hx0, ← hx]; rfl` ([SRC] `padic_zpowers_gen`).
#### Mathlib lemmas needed
`Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_p`, `NNReal.coe_inj`, `inv_ne_zero`, `Nat.cast_ne_zero`, `Nat.Prime.ne_zero`, `Fact.out`, `zpow_mul`, `Subgroup.eq_top_iff'`, `Subgroup.mem_zpowers_iff`, `MonoidWithZeroHom.valueGroup_eq_range`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `Subtype.ext`, `Units.ext`.
#### Sources
[RM] §1.3.5 (Q7.1, 'value group generated by `‖p‖₊ = p⁻¹`'); [Kob84] I §2 (Q7.2); Mathlib `Padic` (Q7.3); decomposition L7.1–L7.4. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`p` any prime (`[Fact p.Prime]`).

### [T033] `ℚ_p` is discretely valued; `p` is a uniformiser and a normalising element
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: T032 · **Parallel**: yes (with T039–T044) · **Type**: instances + theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `isRankOneDiscrete_valuation := inferInstance` (Mathlib supplies `Nontrivial` of the value group); helpers `valueGroupGen_lt_one`, `generator'_eq_valueGroupGen` added (from [SRC]); `NormedField.valuation` written fully qualified inside `namespace Padic` (clash with `Padic.valuation`).
- **Leaves**: L7.5–L7.9

#### Statement
```lean
instance isCyclic_valueGroup :
    IsCyclic (valueGroup (.ofClass (NormedField.valuation (K := ℚ_[p])))) := by sorry
theorem isRankOneDiscrete_valuation : (NormedField.valuation (K := ℚ_[p])).IsRankOneDiscrete := by sorry
theorem coe_generator_eq :
    (generator (NormedField.valuation (K := ℚ_[p])) : ℝ≥0) = (p : ℝ≥0)⁻¹ := by sorry
theorem isUniformizer_p : IsUniformizer (NormedField.valuation (K := ℚ_[p])) (p : ℚ_[p]) := by sorry
instance isCommensurable_p : (NormedField.valuation (K := ℚ_[p])).IsCommensurable (p : ℚ_[p]) := by
  sorry
```
#### Proof sketch
1. `isCyclic_valueGroup`: `isCyclic_iff_exists_zpowers_eq_top.mpr ⟨valueGroupGen, zpowers_valueGroupGen⟩`.
2. `isRankOneDiscrete_valuation`: `inferInstance` (`Valuation.IsRankOneDiscrete.mk'` with `isCyclic_valueGroup` and
   Mathlib's `Nontrivial (valueGroup …)` from `IsNontrivial`, part of the `RankOne` instance of
   `NormedField.valuation`). If instance search fails, provide `Nontrivial` explicitly: `⟨valueGroupGen, 1, fun h ↦
   absurd (congrArg (fun z ↦ ((z : ℝ≥0ˣ) : ℝ≥0)) h) (by simpa [valueGroupGen, nnnorm_p_eq_inv] using …)⟩` as in [SRC].
3. `coe_generator_eq`: `h : generator' (valuation) = valueGroupGen := LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
   (generator'_lt_one _) (valueGroupGen_lt_one) (by rw [generator'_zpowers_eq_top, zpowers_valueGroupGen])` where
   `valueGroupGen_lt_one : valueGroupGen < 1` is `‖p‖₊ < 1` (`Padic.norm_p_lt_one`, `Subtype.coe_lt_coe`,
   `Units.val_lt_val`); then `rw [← nnnorm_p_eq_inv]; exact congrArg (fun z : valueGroup _ ↦ ((z : ℝ≥0ˣ) : ℝ≥0)) h`
   (`embedding_generator'`). ([SRC] `padic_generator'_eq`, `padic_generator_eq`.)
4. `isUniformizer_p`: `rw [Valuation.IsUniformizer.iff, valuation_apply]; exact_mod_cast (nnnorm_p_eq_inv.trans
   coe_generator_eq.symm)` (as `ℝ≥0` values; `Units.val` injective).
5. `isCommensurable_p`: `Valuation.IsRankOneDiscrete.isCommensurable _ isUniformizer_p`.
#### Mathlib lemmas needed
`isCyclic_iff_exists_zpowers_eq_top`, `Valuation.IsRankOneDiscrete.mk'`, `LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq`, `Valuation.IsRankOneDiscrete.generator'_lt_one`, `Valuation.IsRankOneDiscrete.generator'_zpowers_eq_top`, `Valuation.IsRankOneDiscrete.embedding_generator'`, `Valuation.IsUniformizer.iff`, `Padic.norm_p_lt_one`, `Subtype.coe_lt_coe`, `Units.val_lt_val`, `NormedField.valuation_apply`.
#### Sources
[RM] §1.3.5 (Q7.1); [Gou20] 6.4.4 (`π = p` when `e = 1`, Q5.5); decomposition L7.5–L7.9. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`p` any prime. `isCyclic_valueGroup` and `isCommensurable_p` are instances; `isRankOneDiscrete_valuation` is a theorem (the instance is `mk'`).

### [T034] `‖x‖ = p ^ (-normAddValZ x)` and `normAddValZ ℚ_[p] x = Padic.addValuation x`
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: T033 · **Parallel**: yes (with T039–T044) · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): ported from [SRC], with L6.15 at `π = p`.
- **Leaves**: L7.10, L7.11

#### Statement
```lean
theorem norm_eq_zpow_neg_normAddValZ_padic {x : ℚ_[p]} {d : ℤ}
    (hd : normAddValZ ℚ_[p] x = (d : WithTop ℤ)) : ‖x‖ = (p : ℝ) ^ (-d) := by sorry
theorem normAddValZ_padic_apply (x : ℚ_[p]) : normAddValZ ℚ_[p] x = Padic.addValuation x := by sorry
```
#### Proof sketch
1. `norm_eq_zpow_neg_normAddValZ_padic`: `exact norm_eq_zpow_neg_normAddValZ_of_isUniformizer ℚ_[p]
   Padic.isUniformizer_p Padic.norm_p hd` (`‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹`).
2. `normAddValZ_padic_apply`: `by_cases hx : x = 0`. `subst hx; rw [normAddValZ_zero, AddValuation.map_zero]`. Else
   `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top ℚ_[p]).not.mpr hx)`; `rw [← hd,
   Padic.addValuation.apply hx]; congr 1`; `hn1 := norm_eq_zpow_neg_normAddValZ_padic hd.symm`; `hn2 :=
   Padic.norm_eq_zpow_neg_valuation hx`; `hpp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt`;
   `have := (zpow_right_strictMono₀ hpp).injective (hn1.symm.trans hn2); omega` ([SRC] `normAddValZ_padic`).
#### Mathlib lemmas needed
`Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.addValuation.apply`, `AddValuation.map_zero`, `WithTop.ne_top_iff_exists`, `zpow_right_strictMono₀`, `Nat.Prime.one_lt`.
#### Sources
[RM] §1.3.5 (Q7.1); [Kob84] I §2 (Q7.2); decomposition L7.10–L7.11. [SRC] is read-only: port with the new names, never `import PhD.Main.*`.
#### Generality decision
`p` any prime.

### [CLEANUP-14] Run /cleanup on `Padic.lean`
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: T034 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [CLEANUP-ALL-3] Run /cleanup-all before milestone M3 (T035)
- **Status**: done (2026-10-06) · **Depends on**: CLEANUP-14, CLEANUP-10, CLEANUP-13 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: sweep done before the milestone: every finished module builds without warnings, `runLinter` clean, `#print axioms` standard on all declarations of the layer (`scratch/axioms.py`, 143 public declarations).
- Sweep before the milestone: `Discrete.lean`, `Normed.lean`, `Padic.lean` (so far). Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T035] `normAddValZ ℚ_[p] = Padic.addValuation` as additive valuations
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: CLEANUP-ALL-3 · **Parallel**: no · **Type**: theorem · **Milestone**: M3 — `NormedField.normAddValZ_padic` ([RM] §1.3.5): the general construction reproduces Mathlib's `p`-adic valuation. `#print axioms` must be standard.
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `AddValuation.ext normAddValZ_padic_apply`. M3 reached; std axioms.
- **Leaves**: L7.12

#### Statement
```lean
theorem normAddValZ_padic : normAddValZ ℚ_[p] = Padic.addValuation := by sorry
```
#### Proof sketch
1. `AddValuation.ext normAddValZ_padic_apply`.
#### Mathlib lemmas needed
`AddValuation.ext`.
#### Sources
[RM] §1.3.5 (Q7.1, 'as additive valuations'); decomposition L7.12.
#### Generality decision
`p` any prime.

### [CLEANUP-15] Run /cleanup on `Padic.lean`
- **Status**: done (2026-10-06) · **File**: `Padic.lean` · **Depends on**: T035 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T036] The `X`-adic valuation of a nonzero Laurent series is `exp (-order)`
- **Status**: done (2026-10-06) · **File**: `LaurentSeries.lean` · **Depends on**: CLEANUP-10 · **Parallel**: yes (with T025–T031) · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): as planned (`powerSeriesPart` has valuation 1 since its constant coefficient is `f.coeff f.order ≠ 0`; `generalize` + `exp_log` + `omega`). `HahnSeries.coeff_order_eq_zero.not.mpr` replaces the non-existent `coeff_order_ne_zero`.
- **Leaves**: L8.1

#### Statement
```lean
theorem valuation_eq_exp_neg_order {f : LaurentSeries K} (hf : f ≠ 0) :
    Valued.v f = exp (-f.order) := by sorry
```
#### Proof sketch
1. `conv_lhs => rw [← f.single_order_mul_powerSeriesPart]`; `rw [map_mul, LaurentSeries.valuation_single_zpow]`.
2. `hF : Valued.v (f.powerSeriesPart : LaurentSeries K) = 1`: `le_antisymm ((PowerSeries.idealX K).valuation_le_one _)
   ?_`; for `1 ≤ v F`: by contradiction `h : v F < 1`; in `ℤᵐ⁰`, `v F ≠ 0` (`F ≠ 0`: its constant coefficient is
   `f.coeff f.order ≠ 0` by `LaurentSeries.powerSeriesPart_coeff f 0` and `HahnSeries.coeff_order_eq_zero.not.mpr hf`),
   so `v F = exp k` with `k < 0` (`WithZero.exp_log`, `WithZero.exp_lt_exp`), i.e. `k ≤ -1` and `v F ≤ exp (-1)`
   (`WithZero.exp_le_exp`, `Int.lt_iff_add_one_le`); then `(LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero K F
   (d := 1)).mp this 0 zero_lt_one : PowerSeries.coeff 0 F = 0`, contradiction.
3. `rw [hF, mul_one]`.
(New; the Mathlib file states only the `≤` characterisation, decomposition L8.1.)
#### Mathlib lemmas needed
`LaurentSeries.single_order_mul_powerSeriesPart`, `LaurentSeries.valuation_single_zpow`, `LaurentSeries.powerSeriesPart_coeff`, `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`, `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`, `HahnSeries.coeff_order_eq_zero`, `WithZero.exp_log`, `WithZero.exp_lt_exp`, `WithZero.exp_le_exp`, `Int.lt_iff_add_one_le`, `map_mul`, `mul_one`, `le_antisymm`.
#### Sources
[RM] §1.3.5 (Q8.1) and Examples ('the order of vanishing'); Mathlib docstring (Q8.2); [BGR] 1.5.2 Prop. 1 (Q8.3); decomposition L8.1.
#### Generality decision
Any field `K` (the roadmap's `𝔽_q` is an instance); stated for `Valued.v`, not a norm (plan D1).

### [T037] The `X`-adic valuation is discrete; its generator is `exp (-1)`; `X` is a uniformiser
- **Status**: done (2026-10-06) · **File**: `LaurentSeries.lean` · **Depends on**: T036 · **Parallel**: yes (with T025–T031) · **Type**: instance + theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `IsRankOneDiscrete.mk'` after an explicit `IsNontrivial` witness `X`; cyclicity is Mathlib's `IsCyclic (WithZero G)ˣ` instance.
- **Leaves**: L8.2–L8.4

#### Statement
```lean
instance isRankOneDiscrete_valued :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).IsRankOneDiscrete := by sorry
theorem generator_valued_eq :
    generator (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      = Units.mk0 (exp (-1 : ℤ)) exp_ne_zero := by sorry
theorem isUniformizer_X :
    IsUniformizer (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      ((PowerSeries.X : PowerSeries K) : LaurentSeries K) := by sorry
```
#### Proof sketch
1. `isRankOneDiscrete_valued`: first try `inferInstance`. Otherwise `Valuation.IsRankOneDiscrete.mk' _` after
   providing: `Nontrivial (valueGroup (.ofClass (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)))` — from Mathlib's
   `Valuation.IsNontrivial ((PowerSeries.idealX K).valuation (LaurentSeries K))` (`LaurentSeries.valuation_def` is
   `rfl`, so `inferInstanceAs` works) through the `IsNontrivial → Nontrivial valueGroup` instance; and `IsCyclic
   (valueGroup …)`: `haveI : IsCyclic (ℤᵐ⁰ˣ) := isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm
   WithZero.unitsWithZeroEquiv.symm.surjective` (with `isCyclic_multiplicative` for `Multiplicative ℤ`), then
   `Subgroup.isCyclic _`.
2. `generator_valued_eq`: `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
   (LaurentSeries.valuation_surjective K)`.
3. `isUniformizer_X`: `rw [Valuation.IsUniformizer.iff, generator_valued_eq, Units.val_mk0]; simpa using
   LaurentSeries.valuation_X_pow K 1` (`pow_one`, `Nat.cast_one`, `PowerSeries.coe_pow`).
(New; decomposition L8.2–L8.4.)
#### Mathlib lemmas needed
`Valuation.IsRankOneDiscrete.mk'`, `LaurentSeries.valuation_def`, `LaurentSeries.valued`, `isCyclic_of_surjective`, `isCyclic_multiplicative`, `WithZero.unitsWithZeroEquiv`, `Subgroup.isCyclic`, `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective`, `LaurentSeries.valuation_surjective`, `Valuation.IsUniformizer.iff`, `Units.val_mk0`, `LaurentSeries.valuation_X_pow`, `PowerSeries.coe_pow`.
#### Sources
[RM] §1.3.5 (Q8.1, 'at the uniformiser `t`'); Mathlib (Q8.2); decomposition L8.2–L8.4.
#### Generality decision
Any field `K`.

### [T038] `addValZ` on Laurent series: `X ↦ 1`, `single s 1 ↦ s`, `f ↦ f.order`
- **Status**: done (2026-10-06) · **File**: `LaurentSeries.lean` · **Depends on**: T037 · **Parallel**: yes (with T025–T031) · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `exp (-s) = exp (-1) ^ s` by `← exp_zsmul`; `addValZ_eq_order` from T036.
- **Leaves**: L8.5–L8.7

#### Statement
```lean
theorem addValZ_X :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      ((PowerSeries.X : PowerSeries K) : LaurentSeries K) = 1 := by sorry
theorem addValZ_single (s : ℤ) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (HahnSeries.single s (1 : K))
      = (s : WithTop ℤ) := by sorry
theorem addValZ_eq_order {f : LaurentSeries K} (hf : f ≠ 0) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f = (f.order : WithTop ℤ) := by sorry
```
#### Proof sketch
1. `addValZ_X`: `Valuation.IsRankOneDiscrete.addValZ_isUniformizer _ (isUniformizer_X K)`.
2. Helper (inline or private): `hX : Valued.v ((PowerSeries.X : PowerSeries K) : LaurentSeries K) = WithZero.exp (-1)`
   from `valuation_X_pow K 1`; and `hexp : ∀ s : ℤ, WithZero.exp (-s) = WithZero.exp (-1 : ℤ) ^ s` by `rw [←
   WithZero.exp_zsmul]; congr 1; simp` (`smul_neg`, `zsmul_one`/`mul_neg_one`).
3. `addValZ_single`: `Valuation.IsRankOneDiscrete.addValZ_eq_of_zpow _ (isUniformizer_X K) (by rw
   [LaurentSeries.valuation_single_zpow, hX, hexp])`.
4. `addValZ_eq_order`: same with `valuation_eq_exp_neg_order K hf` in place of `valuation_single_zpow`.
(New; decomposition L8.5–L8.7.)
#### Mathlib lemmas needed
`LaurentSeries.valuation_single_zpow`, `LaurentSeries.valuation_X_pow`, `WithZero.exp_zsmul`, `smul_neg`, `zsmul_one`.
#### Sources
[RM] §1.3.5 and Examples (Q8.1); Mathlib (Q8.2); decomposition L8.5–L8.7.
#### Generality decision
Any field `K`.

### [CLEANUP-16] Run /cleanup on `LaurentSeries.lean`
- **Status**: done (2026-10-06) · **File**: `LaurentSeries.lean` · **Depends on**: T038 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T039] Commensurability passes to the completion of a valued field
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: CLEANUP-13 · **Parallel**: yes (with T032–T035) · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): via `Valued.exists_coe_eq_v`; the anonymous instance is recovered by `inferInstance`.
- **Leaves**: L9.1

#### Statement
```lean
theorem isCommensurable_completion (π : K) [hv.v.IsCommensurable π] :
    (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).IsCommensurable
      (π : UniformSpace.Completion K) := by sorry
```
#### Proof sketch
1. `refine ⟨?_, ?_, fun x hx ↦ ?_⟩`; the first two: `rw [Valued.valuedCompletion_apply]` and use the instance's
   `val_pos`, `val_lt_one` (`Valued.v (π : Completion K) = Valued.v π`).
2. `obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x` — `hr : Valued.extensionValuation x = Valued.v r`, and `Valued.v x`
   on the completion is `Valued.extensionValuation x` by `rfl` (`Valued.valuedCompletion`'s `v` field); `hr0 : Valued.v r ≠ 0
   := hr ▸ hx`; `obtain ⟨m, n, hn, e⟩ := ‹hv.v.IsCommensurable π›.exists_zpow_eq r hr0`; `exact ⟨m, n, hn, by rw
   [show Valued.v x = Valued.v r from hr, Valued.valuedCompletion_apply, e]⟩`.
(New; decomposition L9.1.)
#### Mathlib lemmas needed
`Valued.exists_coe_eq_v`, `Valued.valuedCompletion_apply`, `Valued.valuedCompletion`, `Valued.extensionValuation`, `UniformSpace.Completion.coe'`.
#### Sources
[RM] §1.5.3 (Q9.3); [Gou20] 6.8.7 / Lemma 3.2.10 and [BGR] 1.5.1 (Q9.8); [Kob84] III §4 (Q6.5); decomposition L9.1.
#### Generality decision
Any `[Valued K Γ₀]` field with any `Γ₀` (no rank-one hypothesis; plan D3).

### [T040] `normAddVal` of a normed algebra field restricts to `normAddVal` of the base
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T039 · **Parallel**: yes (with T032–T035) · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `norm_algebraMap'`; no completeness/algebraicity needed (plan D4).
- **Leaves**: L9.2

#### Statement
```lean
theorem normAddVal_algebraMap (x : K) : normAddVal L (algebraMap K L x) = normAddVal K x := by sorry
```
#### Proof sketch
1. `rcases eq_or_ne x 0 with rfl | hx`; zero: `rw [map_zero, normAddVal_zero, normAddVal_zero]`.
2. Nonzero: `rw [normAddVal_apply_of_ne_zero L ((map_ne_zero (algebraMap K L)).mpr hx), normAddVal_apply_of_ne_zero K
   hx, norm_algebraMap']`.
(New; decomposition L9.2.)
#### Mathlib lemmas needed
`norm_algebraMap'`, `map_ne_zero`, `map_zero`.
#### Sources
[RM] §1.5.1 (Q9.1); [BGR] 3.2.4/2 (Q9.6) for the spectral-norm reading; decomposition L9.2.
#### Generality decision
Any ultrametric nontrivially normed `K`-algebra field `L` (no completeness or algebraicity: plan D4).

### [T041] The ramification index exists and is positive; the image of a uniformiser is a normalising element
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T040 · **Parallel**: yes (with T032–T035) · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): positivity of `d` by `zpow_lt_one_iff_right_of_lt_one₀` on `ℝ≥0`.
- **Leaves**: L9.3, L9.5

#### Statement
```lean
theorem exists_normAddValZ_algebraMap_eq {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    ∃ e : ℕ, 0 < e ∧ normAddValZ L (algebraMap K L π) = ((e : ℤ) : WithTop ℤ) := by sorry
theorem isCommensurable_algebraMap_of_isRankOneDiscrete {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) :
    (valuation (K := L)).IsCommensurable (algebraMap K L π) := by sorry
```
#### Proof sketch
1. `exists_normAddValZ_algebraMap_eq`: `hπ0 : algebraMap K L π ≠ 0 := (map_ne_zero _).mpr hπ.ne_zero`; `obtain ⟨d,
   hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hπ0)`; `hv := (IsRankOneDiscrete.addValZ_eq_iff
   _ _ d).mp hd.symm : valuation (algebraMap K L π) = ↑(generator _ ^ d)`; `hlt : valuation (algebraMap K L π) < 1`
   by `valuation_apply`, `← NNReal.coe_lt_coe`, `norm_algebraMap'`, `hπ.val_lt_one` (via `valuation_apply` on `K`);
   `hd0 : 0 < d`: from `hv ▸ hlt : ↑(generator ^ d) < 1` → `generator ^ d < 1` in `Γ₀ˣ = ℝ≥0ˣ` (`Units.val_lt_val`) and
   `generator < 1` (`generator_lt_one`): `(zpow_lt_one_iff_right_of_lt_one₀ … ).mp` (on the group of units, or on
   `ℝ≥0` after `Units.val_zpow_eq_zpow_val`, using `generator_ne_zero` for positivity); `exact ⟨d.toNat, Int.toNat_pos.mpr
   hd0 ⊢ by omega, by rw [Int.toNat_of_nonneg hd0.le]; exact hd.symm⟩`.
2. `isCommensurable_algebraMap_of_isRankOneDiscrete`: `IsRankOneDiscrete.isCommensurable_of_lt_one _ ((map_ne_zero
   _).mpr hπ.ne_zero |> (Valuation.ne_zero_iff _).mpr) hlt` with `hlt` as above.
(New; decomposition L9.3, L9.5.)
#### Mathlib lemmas needed
`map_ne_zero`, `Valuation.IsUniformizer.ne_zero`, `Valuation.IsUniformizer.val_lt_one`, `WithTop.ne_top_iff_exists`, `Valuation.IsRankOneDiscrete.generator_lt_one`, `Valuation.IsRankOneDiscrete.generator_ne_zero`, `NNReal.coe_lt_coe`, `norm_algebraMap'`, `Units.val_lt_val`, `Units.val_zpow_eq_zpow_val`, `zpow_lt_one_iff_right_of_lt_one₀`, `Int.toNat_of_nonneg`, `Valuation.ne_zero_iff`.
#### Sources
[RM] §1.3.6 (Q9.4); [Gou20] 6.4.3 and [BGR] 3.1.3 (Q9.7); [Kob84] III §3 (Q5.4); decomposition L9.3, L9.5.
#### Generality decision
Both discreteness hypotheses as instances; no finiteness (plan D2).

### [CLEANUP-17] Run /cleanup on `Extension.lean`
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T041 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [CLEANUP-ALL-4] Run /cleanup-all before milestone M4 (T042)
- **Status**: done (2026-10-06) · **Depends on**: CLEANUP-17 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: sweep done before the milestone: every finished module builds without warnings, `runLinter` clean, `#print axioms` standard on all declarations of the layer (`scratch/axioms.py`, 143 public declarations).
- Sweep before the milestone: `Extension.lean` (so far) and every module it imports that changed since CLEANUP-ALL-3. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T042] The ramification formula `normAddValZ L (algebraMap x) = e * normAddValZ K x`
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: CLEANUP-ALL-4 · **Parallel**: no · **Type**: theorem · **Milestone**: M4 — `NormedField.normAddValZ_algebraMap` ([RM] §1.3.6, with `e` defined by `he`). `#print axioms` must be standard.
- **Progress**: 2026-10-06 (session 18:50–19:25Z): one `rw` chain after `addValZ_eq_iff` (`zpow_mul`, `← hπL`, norms). M4 reached; std axioms.
- **Leaves**: L9.4

#### Statement
```lean
theorem normAddValZ_algebraMap {π : K} (hπ : IsUniformizer (valuation (K := K)) π) {e : ℤ}
    (he : normAddValZ L (algebraMap K L π) = (e : WithTop ℤ)) (x : K) :
    normAddValZ L (algebraMap K L x) = WithTop.map (fun k : ℤ ↦ e * k) (normAddValZ K x) := by sorry
```
#### Proof sketch
1. `rcases eq_or_ne x 0 with rfl | hx`; zero: `rw [map_zero, normAddValZ_zero, normAddValZ_zero, WithTop.map_top]`.
2. `obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)`; `rw [← hk, WithTop.map_coe]`.
3. `hxK : ‖x‖ = ‖π‖ ^ k := (normAddValZ_eq_iff_of_isUniformizer K hπ x k).mp hk.symm`; `hxL : ‖algebraMap K L x‖ =
   ‖algebraMap K L π‖ ^ k := by rw [norm_algebraMap', norm_algebraMap', hxK]`.
4. `hπL : valuation (algebraMap K L π) = ↑(generator _ ^ e) := (IsRankOneDiscrete.addValZ_eq_iff _ _ e).mp he`.
5. `refine (IsRankOneDiscrete.addValZ_eq_iff _ _ (e * k)).mpr ?_`; `rw [valuation_apply, ← NNReal.coe_inj, coe_nnnorm,
   hxL, ← coe_nnnorm, ← valuation_apply, hπL, NNReal.coe_zpow, ← Units.val_zpow_eq_zpow_val, ← zpow_mul]`; finish
   with `Units.val_zpow_eq_zpow_val`/`NNReal.coe_zpow` so both sides read `((generator : ℝ≥0) : ℝ) ^ (e * k)`.
(New; decomposition L9.4 — the prose is [Kob84]'s `m = e · ord_p x`.)
#### Mathlib lemmas needed
`WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `norm_algebraMap'`, `NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`, `Units.val_zpow_eq_zpow_val`, `zpow_mul`, `map_zero`.
#### Sources
[RM] §1.3.6 (Q9.4); [Kob84] III §3 (Q5.4, `m = e·ord_p x`); [Gou20] 6.4.3 (Q9.7); decomposition L9.4.
#### Generality decision
`e : ℤ` pinned by `he` (positive by T041); no finiteness, completeness or algebraicity (plan D2).

### [T043] `normAddValZ L` is `e` times `normAddValQ L` normalised at the uniformiser of `K`
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T042 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `e > 0` recovered from `exists_normAddValZ_algebraMap_eq`; workhorse then `field_simp`.
- **Leaves**: L9.6

#### Statement
```lean
theorem map_intCast_normAddValZ_eq_map_normAddValQ {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) {e : ℤ}
    (he : normAddValZ L (algebraMap K L π) = (e : WithTop ℤ))
    [(valuation (K := L)).IsCommensurable (algebraMap K L π)] (y : L) :
    WithTop.map (fun n : ℤ ↦ (n : ℚ)) (normAddValZ L y)
      = WithTop.map (fun q : ℚ ↦ (e : ℚ) * q) (normAddValQ L (algebraMap K L π) y) := by sorry
```
#### Proof sketch
1. `he_pos : 0 < e`: as in T041 step 1 from `he` (`addValZ_eq_iff`, `‖algebraMap π‖ < 1`, `generator < 1`).
2. `rcases eq_or_ne y 0 with rfl | hy`; zero: `rw [normAddValZ_zero, normAddValQ_zero, WithTop.map_top, WithTop.map_top]`.
3. `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hy)`; `hyv := (IsRankOneDiscrete.addValZ_eq_iff
   _ _ d).mp hd.symm`; `hπv := (IsRankOneDiscrete.addValZ_eq_iff _ _ e).mp he`.
4. `hpow : valuation y ^ e = valuation (algebraMap K L π) ^ d := by rw [hyv, hπv, ← Units.val_zpow_eq_zpow_val, ←
   Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_mul, mul_comm]`.
5. `rw [← hd, WithTop.map_coe, normAddValQ, addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr hy) he_pos hpow,
   WithTop.map_coe, WithTop.coe_inj]`; `field_simp`/`mul_div_cancel₀ _ (by exact_mod_cast he_pos.ne' : (e : ℚ) ≠ 0)`.
(New; decomposition L9.6.)
#### Mathlib lemmas needed
`WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `WithTop.coe_inj`, `Units.val_zpow_eq_zpow_val`, `zpow_mul`, `mul_comm`, `Valuation.ne_zero_iff`, `mul_div_cancel₀`.
#### Sources
[RM] §1.3.6 (Q9.4, second sentence); decomposition L9.6.
#### Generality decision
As T042; the `IsCommensurable` instance on `L` is a hypothesis (T041 derives it).

### [T044] `‖x‖ ^ n = ‖a₀‖` for the minimal polynomial; commensurability is inherited by algebraic extensions; `normAddValQ` restricts
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T043 · **Parallel**: no · **Type**: theorem + instance + theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `NormedAlgebra.norm_eq_spectralNorm` + `spectralNorm_eq_norm_coeff_zero_rpow` + `Real.rpow_inv_natCast_pow`; `omit [IsUltrametricDist L] in` on `norm_pow_natDegree_minpoly` (unused, linter).
- **Leaves**: L9.7–L9.9

#### Statement
```lean
theorem norm_pow_natDegree_minpoly [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by sorry
instance isCommensurable_algebraMap [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K)
    [(valuation (K := K)).IsCommensurable π] :
    (valuation (K := L)).IsCommensurable (algebraMap K L π) := by sorry
theorem normAddValQ_algebraMap [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K)
    [(valuation (K := K)).IsCommensurable π] (x : K) :
    normAddValQ L (algebraMap K L π) (algebraMap K L x) = normAddValQ K π x := by sorry
```
#### Proof sketch
1. `norm_pow_natDegree_minpoly`: `rw [NormedAlgebra.norm_eq_spectralNorm K x, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
   one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne']`
   (the `IsUltrametricDist K` instance is what `NormedAlgebra.norm_eq_spectralNorm` needs; `K` complete).
2. `isCommensurable_algebraMap`: `refine ⟨?_, ?_, fun x hx ↦ ?_⟩`; `val_pos`/`val_lt_one` via `valuation_apply`,
   `nnnorm_algebraMap'` and the instance on `K`. For `x`: `hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hx`; `set n :=
   (minpoly K x).natDegree`, `hn : 0 < n := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)`; `a₀ := (minpoly K
   x).coeff 0`, `ha₀ : a₀ ≠ 0 := minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx0`; `obtain ⟨m, k, hk, e⟩
   := ‹(valuation (K := K)).IsCommensurable π›.exists_zpow_eq a₀ ((Valuation.ne_zero_iff _).mpr ha₀)`; `hxn : ‖x‖₊ ^ n =
   ‖a₀‖₊ := by rw [← NNReal.coe_inj]; push_cast; exact norm_pow_natDegree_minpoly x`; `refine ⟨m, n * k, mul_pos
   (Nat.cast_pos.mpr hn) hk, ?_⟩`; `rw [valuation_apply, valuation_apply, nnnorm_algebraMap', zpow_mul, zpow_natCast,
   hxn]; exact_mod_cast e` (the instance on `K` is stated with `valuation_apply`-free `v`; unfold with `valuation_apply`).
3. `normAddValQ_algebraMap`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `map_zero`, `normAddValQ_zero` twice);
   `obtain ⟨m, n, hn, e⟩ := ‹_›.exists_zpow_eq x ((Valuation.ne_zero_iff _).mpr hx)`; `e' : valuation (algebraMap K L x)
   ^ n = valuation (algebraMap K L π) ^ m := by rw [valuation_apply, valuation_apply, nnnorm_algebraMap',
   nnnorm_algebraMap']; exact e`; `rw [normAddValQ, normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hx) hn e',
   addValQ_eq_of_zpow _ _ _ hn e]`.
(New; decomposition L9.7–L9.9; the `[CompleteSpace K] [Algebra.IsAlgebraic K L]` binders are the D1 repair.)
#### Mathlib lemmas needed
`NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `Real.rpow_inv_natCast_pow`, `minpoly.natDegree_pos`, `minpoly.coeff_zero_ne_zero`, `Algebra.IsIntegral.isIntegral`, `norm_nonneg`, `one_div`, `nnnorm_algebraMap'`, `NormedField.valuation_apply`, `Valuation.ne_zero_iff`, `NNReal.coe_inj`, `zpow_mul`, `zpow_natCast`, `Nat.cast_pos`, `mul_pos`, `map_zero`.
#### Sources
[RM] §1.5.2 (Q9.2; route through BGR 3.2.4/3 = Q9.5 rather than the `i`-th coefficient); [BGR] 3.2.4/2 (Q9.6); [Kob84] III §2 (Q9.9); [Gou20] 6.3.4–6.3.5; decomposition L9.7–L9.9.
#### Generality decision
`[CompleteSpace K] [Algebra.IsAlgebraic K L]` explicit on each declaration (D1); `L` any ultrametric nontrivially normed `K`-algebra field (the spectral norm by Mathlib's uniqueness), so `PadicAlgCl p` is an instance.

### [CLEANUP-18] Run /cleanup on `Extension.lean`
- **Status**: done (2026-10-06) · **File**: `Extension.lean` · **Depends on**: T044 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T045] Every algebraic ultrametric normed `ℚ_p`-algebra field is commensurable at `p`; the algebraic closure of `ℚ_p`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: CLEANUP-15, CLEANUP-18 · **Parallel**: no · **Type**: instance + theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `isCommensurable_algebraMap` at `K = ℚ_[p]` + `map_natCast`; `PadicAlgCl.isCommensurable_p := inferInstance`.
- **Leaves**: L10.1, L10.2

#### Statement
```lean
instance isCommensurable_natCast_prime {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] [NormedAlgebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L] :
    (valuation (K := L)).IsCommensurable (p : L) := by sorry
theorem isCommensurable_p : (valuation (K := PadicAlgCl p)).IsCommensurable (p : PadicAlgCl p) := by sorry
```
#### Proof sketch
1. `isCommensurable_natCast_prime`: `have := NormedField.isCommensurable_algebraMap (K := ℚ_[p]) (L := L) (p : ℚ_[p])`
   (instances: `Padic.isCommensurable_p`, `CompleteSpace ℚ_[p]`); `rwa [map_natCast] at this`.
2. `PadicAlgCl.isCommensurable_p`: `inferInstance` (step 1 with `L := PadicAlgCl p`; Mathlib's `PadicAlgCl.normedAlgebra`,
   `PadicAlgCl.isAlgebraic`, `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`).
(New; decomposition L10.1–L10.2.)
#### Mathlib lemmas needed
`map_natCast`, `PadicAlgCl.normedAlgebra`, `PadicAlgCl.isAlgebraic`, `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`.
#### Sources
[RM] §1.5.4 (Q10.1, first half) via §1.5.2 (Q9.2); [Kob84] III §3 (Q10.3); decomposition L10.1–L10.2.
#### Generality decision
`L` any algebraic ultrametric nontrivially normed `ℚ_p`-algebra field; the instance's element is `(p : L)` (a `Nat.cast`), so instance search finds it on `(p : PadicAlgCl p)`.

### [T046] `ℂ_p`: the extended valuation is `‖·‖₊`; `ℂ_p` is commensurable at `p`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: T045 · **Parallel**: no · **Type**: theorems + instance
- **Progress**: 2026-10-06 (session 18:50–19:25Z): seam `Valued.v = NormedField.valuation` on `ℂ_[p]` proved from `PadicComplex.norm_eq_norm p`; commensurability from T039 + `PadicComplex.coe_natCast`.
- **Leaves**: L10.3–L10.5

#### Statement
```lean
theorem valuation_eq_nnnorm (x : ℂ_[p]) : Valued.v x = ‖x‖₊ := by sorry
theorem normedField_valuation_eq : (valuation (K := ℂ_[p])) = (PadicComplex.valued p).v := by sorry
instance isCommensurable_p : (valuation (K := ℂ_[p])).IsCommensurable (p : ℂ_[p]) := by sorry
```
#### Proof sketch
1. `valuation_eq_nnnorm`: `rw [← NNReal.coe_inj, coe_nnnorm, PadicComplex.norm_eq_norm x, Valuation.norm_def,
   PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]`.
2. `normedField_valuation_eq`: `Valuation.ext fun x ↦ by rw [NormedField.valuation_apply, valuation_eq_nnnorm]`.
3. `isCommensurable_p`: `h₀ : (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).IsCommensurable (p : PadicAlgCl p) :=
   PadicAlgCl.isCommensurable_p` (`PadicAlgCl.valued` is `NormedField.toValued`, so `Valued.v = NormedField.valuation`
   by `rfl`; if needed `Valuation.IsCommensurable.of_forall_eq _ _ fun x ↦ PadicAlgCl.valuation_def x`); `h₁ :=
   Valued.isCommensurable_completion (K := PadicAlgCl p) (p : PadicAlgCl p)` (T039; `UniformSpace.Completion
   (PadicAlgCl p)` is `ℂ_[p]` by `abbrev`); `rw [normedField_valuation_eq]`; `simpa only [PadicComplex.coe_natCast,
   PadicComplex.coe_eq] using h₁` (the element `((p : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p])`).
(New; decomposition L10.3–L10.5.)
#### Mathlib lemmas needed
`PadicComplex.norm_eq_norm`, `PadicComplex.RankOne.hom_eq_embedding`, `Valuation.norm_def`, `Valuation.embedding_restrict`, `NNReal.coe_inj`, `coe_nnnorm`, `Valuation.ext`, `NormedField.valuation_apply`, `PadicAlgCl.valuation_def`, `PadicAlgCl.valued`, `PadicComplex.valued`, `PadicComplex.coe_natCast`, `PadicComplex.coe_eq`, `PadicComplex.valuation_extends`.
#### Sources
[RM] §1.5.4 (Q10.1) via §1.5.3 (Q9.3); [Gou20] 6.8.6–6.8.7 (Q10.4); [Kob84] III §4 (Q10.3); Mathlib `PadicComplex` (Q10.5); decomposition L10.3–L10.5.
#### Generality decision
`p` any prime; the seam `Valued.v = NormedField.valuation` on `ℂ_[p]` is a theorem, not an assumption.

### [T047] `normAddValQ ℂ_[p] p`: `p ↦ 1`, restriction to `ℚ_p` is `Padic.addValuation`, `‖x‖ = p ^ (-q)`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: T046 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): restriction to `ℚ_p` by the workhorse with `n = 1`; norm recovery by `Real.inv_rpow`, `Real.rpow_neg`.
- **Leaves**: L10.6–L10.8

#### Statement
```lean
theorem normAddValQ_p : normAddValQ ℂ_[p] p p = 1 := by sorry
theorem normAddValQ_algebraMap_padic (x : ℚ_[p]) :
    normAddValQ ℂ_[p] p (algebraMap ℚ_[p] ℂ_[p] x)
      = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (Padic.addValuation x) := by sorry
theorem norm_eq_rpow_neg_normAddValQ {x : ℂ_[p]} {q : ℚ}
    (hq : normAddValQ ℂ_[p] p x = (q : WithTop ℚ)) : ‖x‖ = (p : ℝ) ^ (-(q : ℝ)) := by sorry
```
#### Proof sketch
1. `normAddValQ_p`: `normAddValQ_self _ _`.
2. `normAddValQ_algebraMap_padic`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `map_zero`, `normAddValQ_zero`,
   `AddValuation.map_zero`, `WithTop.map_top`); `rw [Padic.addValuation.apply hx, WithTop.map_coe]`; `hp : ‖(p : ℂ_[p])‖₊
   = ‖(p : ℚ_[p])‖₊ := by rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p])]; exact PadicComplex.nnnorm_extends' _` (or
   `nnnorm_algebraMap'`); `hxv : valuation (algebraMap ℚ_[p] ℂ_[p] x) ^ (1 : ℤ) = valuation (p : ℂ_[p]) ^ x.valuation
   := by rw [zpow_one, valuation_apply, valuation_apply, nnnorm_algebraMap', hp, Padic.nnnorm_p_zpow_valuation hx]`;
   `rw [normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hx) one_pos hxv]; norm_num`.
3. `norm_eq_rpow_neg_normAddValQ`: `rw [norm_eq_norm_rpow_normAddValQ _ _ hq]`; `hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
   rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]`; `rw [hp, Real.inv_rpow (by
   positivity), ← Real.rpow_neg (by positivity)]`.
(New; decomposition L10.6–L10.8.)
#### Mathlib lemmas needed
`Padic.addValuation.apply`, `Padic.norm_p`, `PadicComplex.nnnorm_extends'`, `nnnorm_algebraMap'`, `norm_algebraMap'`, `map_natCast`, `zpow_one`, `WithTop.map_top`, `WithTop.map_coe`, `AddValuation.map_zero`, `Real.inv_rpow`, `Real.rpow_neg`, `NormedField.valuation_apply`.
#### Sources
[RM] §1.5.4 (Q10.1); [Gou20] 6.8.7 (Q10.4); decomposition L10.6–L10.8.
#### Generality decision
`p` any prime.

### [CLEANUP-19] Run /cleanup on `PadicComplex.lean`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: T047 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>`; lines ≤ 100 characters; no deprecated names; golf to [SRC] quality or better; do not touch declarations that are still `sorry`.

### [CLEANUP-ALL-5] Run /cleanup-all before milestone M5 (T048)
- **Status**: done (2026-10-06) · **Depends on**: CLEANUP-19, CLEANUP-15, CLEANUP-16 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: sweep done before the milestone: every finished module builds without warnings, `runLinter` clean, `#print axioms` standard on all declarations of the layer (`scratch/axioms.py`, 143 public declarations).
- Sweep before the milestone: `Padic.lean`, `LaurentSeries.lean`, `Extension.lean`, `PadicComplex.lean` (so far). Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T048] Every rational is a value; the value group of `ℂ_p` is exactly `p^ℚ`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: CLEANUP-ALL-5 · **Parallel**: no · **Type**: theorems · **Milestone**: M5 — `PadicComplex.range_normAddValQ` with `PadicComplex.isCommensurable_p` ([RM] §1.5.4–§1.5.5, convention 8). `#print axioms` must be standard on both.
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `IsAlgClosed.exists_pow_nat_eq` for `z ^ den = p ^ num`, `Rat.num_div_den`; range by `Set.ext`. M5 reached; std axioms.
- **Leaves**: L10.9, L10.10

#### Statement
```lean
theorem exists_normAddValQ_eq (q : ℚ) :
    ∃ x : ℂ_[p], x ≠ 0 ∧ normAddValQ ℂ_[p] p x = (q : WithTop ℚ) := by sorry
theorem range_normAddValQ :
    Set.range (normAddValQ ℂ_[p] p) = insert ⊤ (Set.range ((↑) : ℚ → WithTop ℚ)) := by sorry
```
#### Proof sketch
1. `exists_normAddValQ_eq`: `hb : 0 < q.den := q.den_pos`; `obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p])
   ^ q.num) hb`; `hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero` (`CharZero ℂ_[p]`); `hz0 : z ≠
   0 := fun h ↦ by simp [h, zpow_ne_zero q.num hp0] at hz` (`zero_pow hb.ne'`); `hv : valuation z ^ (q.den : ℤ) =
   valuation (p : ℂ_[p]) ^ q.num := by rw [zpow_natCast, ← map_pow, hz, map_zpow₀]`; `refine ⟨z, hz0, ?_⟩`; `rw
   [normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hz0) (by exact_mod_cast hb) hv, Rat.num_div_den]`.
2. `range_normAddValQ`: `ext y; simp only [Set.mem_range, Set.mem_insert_iff]`; `constructor`; `rintro ⟨x, rfl⟩`:
   `rcases eq_or_ne x 0 with rfl | hx`: `left; exact normAddValQ_zero _ _`; `right; obtain ⟨r, hr⟩ :=
   WithTop.ne_top_iff_exists.mp ((normAddValQ_eq_top _ _).not.mpr hx); exact ⟨r, hr⟩`. Converse: `rintro (rfl | ⟨r,
   rfl⟩)`: `⟨0, normAddValQ_zero _ _⟩`; `obtain ⟨x, -, hx⟩ := exists_normAddValQ_eq r; exact ⟨x, hx⟩`.
(New; decomposition L10.9–L10.10.)
#### Mathlib lemmas needed
`IsAlgClosed.exists_pow_nat_eq`, `PadicComplex.isAlgClosed`, `Rat.den_pos`, `Rat.num_div_den`, `Nat.cast_ne_zero`, `zpow_ne_zero`, `zero_pow`, `zpow_natCast`, `map_pow`, `map_zpow₀`, `Set.mem_range`, `Set.mem_insert_iff`, `WithTop.ne_top_iff_exists`.
#### Sources
[RM] §1.5.5 (Q10.2); [Kob84] III §4 and Exercise 1 (Q10.3); [Gou20] 6.8.7 (Q10.4); decomposition L10.9–L10.10.
#### Generality decision
`p` any prime.

### [CLEANUP-20] Run /cleanup on `PadicComplex.lean`
- **Status**: done (2026-10-06) · **File**: `PadicComplex.lean` · **Depends on**: T048 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T049] `ℚ_p` examples: `normAddValZ p = 1`, `normAddValZ (1/p²) = -2`, `normAddVal = log p · normAddValZ`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: CLEANUP-16, CLEANUP-20 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `Padic.valuation_inv`, `valuation_pow`, `valuation_p`; `log p` square from T029.
- **Leaves**: L11.1–L11.3

#### Statement
```lean
theorem normAddValZ_padic_p : normAddValZ ℚ_[p] (p : ℚ_[p]) = 1 := by sorry
theorem normAddValZ_padic_inv_p_sq :
    normAddValZ ℚ_[p] ((p : ℚ_[p]) ^ 2)⁻¹ = ((-2 : ℤ) : WithTop ℤ) := by sorry
theorem normAddVal_padic (x : ℚ_[p]) :
    normAddVal ℚ_[p] x
      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * Real.log p) (normAddValZ ℚ_[p] x) := by sorry
```
#### Proof sketch
1. `normAddValZ_padic_p`: `normAddValZ_isUniformizer _ Padic.isUniformizer_p`.
2. `normAddValZ_padic_inv_p_sq`: `hp : (p : ℚ_[p]) ≠ 0`; `rw [normAddValZ_padic_apply, Padic.addValuation.apply
   (inv_ne_zero (pow_ne_zero 2 hp)), Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]; norm_num`.
3. `normAddVal_padic`: `rw [normAddVal_eq_map_normAddValZ ℚ_[p] Padic.isUniformizer_p x]; congr 1; funext k; rw
   [Padic.norm_p, Real.log_inv, neg_neg]`.
(decomposition L11.1–L11.3.)
#### Mathlib lemmas needed
`Padic.addValuation.apply`, `Padic.valuation_inv`, `Padic.valuation_pow`, `Padic.valuation_p`, `Padic.norm_p`, `Real.log_inv`, `inv_ne_zero`, `pow_ne_zero`, `neg_neg`.
#### Sources
[RM] Layer 1 Examples (Q11.1); [Kob84] I §2 (Q5.6, Q11.2-style computations); decomposition L11.1–L11.3.
#### Generality decision
`p` any prime.

### [T050] `√p` and `∛p` examples: `normAddValQ = 1/2`, `normAddValZ p = 2`, `normAddValQ ℂ_[p] p (∛p) = 1/3`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T049 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 (session 18:50–19:25Z): workhorse read off norms with explicit `(m := 1) (n := 2/3)`; `omit [Fact p.Prime] [NormedAlgebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L] in` on `normAddValZ_prime_of_sq_eq_prime` (unused, linter).
- **Leaves**: L11.4–L11.6

#### Statement
```lean
theorem normAddValQ_of_sq_eq_prime {s : L} (hs : s ^ 2 = p) :
    normAddValQ L p s = ((1 / 2 : ℚ) : WithTop ℚ) := by sorry
theorem normAddValZ_prime_of_sq_eq_prime [(valuation (K := L)).IsRankOneDiscrete] {s : L}
    (hs : s ^ 2 = p) (h1 : normAddValZ L s = 1) : normAddValZ L (p : L) = 2 := by sorry
theorem normAddValQ_padicComplex_of_pow_three {x : ℂ_[p]} (hx : x ^ 3 = p) :
    normAddValQ ℂ_[p] p x = ((1 / 3 : ℚ) : WithTop ℚ) := by sorry
```
#### Proof sketch
1. `normAddValQ_of_sq_eq_prime`: `hp : (p : L) ≠ 0 := by rw [← map_natCast (algebraMap ℚ_[p] L)]; exact (map_ne_zero
   _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`; `hs0 : s ≠ 0 := fun h ↦ hp (by rw [← hs, h, zero_pow
   two_ne_zero])`; `have := normAddValQ_eq_of_pow_eq_pow L (p : L) hs0 two_pos (m := 1) (by rw [← norm_pow, hs,
   pow_one])`; `simpa using this` (`Nat.cast_one`, `one_div`).
2. `normAddValZ_prime_of_sq_eq_prime`: `rw [← hs, AddValuation.map_pow, h1, two_nsmul, one_add_one_eq_two]`.
3. `normAddValQ_padicComplex_of_pow_three`: as step 1 with `n = 3`, `hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr …`
   (`CharZero ℂ_[p]`), `norm_pow`, `pow_one`.
(decomposition L11.4–L11.6.)
#### Mathlib lemmas needed
`map_natCast`, `map_ne_zero`, `Nat.cast_ne_zero`, `zero_pow`, `norm_pow`, `pow_one`, `two_pos`, `AddValuation.map_pow`, `two_nsmul`, `one_add_one_eq_two`, `PadicComplex.charZero`.
#### Sources
[RM] Layer 1 Examples (Q11.1); [Gou20] Problems 242–244 (computations in `ℚ_5(√2)`, `ℚ_5(√5)`); decomposition L11.4–L11.6; plan D6 for the `ℚ_p(√p)` reading.
#### Generality decision
Any algebraic ultrametric nontrivially normed `ℚ_p`-algebra field `L` with an `s` such that `s ^ 2 = p` (plan D6).

### [T051] Laurent series example: `addValZ (X ^ n) = n`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T050 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 (session 18:50–19:25Z): `AddValuation.map_pow`, `addValZ_X`, `WithTop.coe_nsmul`, `nsmul_one`.
- **Leaves**: L11.7

#### Statement
```lean
theorem addValZ_X_pow (n : ℕ) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ n) = ((n : ℤ) : WithTop ℤ) := by sorry
```
#### Proof sketch
1. `rw [AddValuation.map_pow, LaurentSeries.addValZ_X]`; the goal `n • (1 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`:
   `rw [nsmul_eq_mul, mul_one]; norm_cast` (`WithTop.coe_natCast`).
(decomposition L11.7.)
#### Mathlib lemmas needed
`AddValuation.map_pow`, `nsmul_eq_mul`, `mul_one`, `WithTop.coe_natCast`.
#### Sources
[RM] Layer 1 Examples (Q11.1, `𝔽_q⸨t⸩`); decomposition L11.7.
#### Generality decision
Any field `K`.

### [CLEANUP-21] Run /cleanup on `Examples.lean`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T051 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 (inline, after the proof session): widths ≤ 100 (code points), `lake exe runLinter` clean on the module (simpNF fixes recorded in `plan.md`, Execution notes), redundant Mathlib imports removed by `scratch/prune_imports.py` trials (11 across NegLog, RatLog, Basic, Discrete, Extension) with a full rebuild, module docstring names cross-checked against the declarations.
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances the signature audit flagged.

### [T052] Chain root: build the whole Tau Ceti chain and run the full gate
- **Status**: done (2026-10-06) · **File**: `PhD/TauCeti.lean` · **Depends on**: CLEANUP-2, CLEANUP-3, CLEANUP-4, CLEANUP-5, CLEANUP-8, CLEANUP-10, CLEANUP-13, CLEANUP-15, CLEANUP-16, CLEANUP-18, CLEANUP-20, CLEANUP-21 (every final per-file cleanup) · **Parallel**: no · **Type**: gate
- **Progress**: 2026-10-06: `grep sorry` on `AddVal/` empty; `lake build PhD.TauCeti` → `Build completed successfully (3619 jobs)`, no warnings anywhere in the chain; `runLinter` clean on all twelve modules; `scratch/axioms.py` → 143 public declarations, only `propext`/`Classical.choice`/`Quot.sound` (milestones included); no `import PhD.Main` in `PhD/TauCeti/`.
- **Leaves**: (all)

#### Statement
```lean
-- PhD/TauCeti.lean already imports the board's leaf:
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples
-- Gate (no new declaration): the whole chain builds, the layer is sorry-free, axioms are standard.
```
#### Proof sketch
1. `grep -rn "sorry" PhD/TauCeti/Code/NewtonPolygons/AddVal/` must be empty.
2. `lake build PhD.TauCeti` (the CI gate of the chain; never `lake build PhD`) must pass with no warnings from the
   twelve `AddVal` modules.
3. `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>` for each of the twelve modules: clean.
4. A scratch file importing the leaf with `#print axioms` on the five milestones (`Valuation.addVal_map`,
   `Valuation.addValQ_unique`, `NormedField.normAddValZ_padic`, `NormedField.normAddValZ_algebraMap`,
   `PadicComplex.range_normAddValQ`) and on `PadicComplex.isCommensurable_p`: only `propext`, `Classical.choice`,
   `Quot.sound`.
5. Confirm no file imports `PhD.Main.*` (`grep -rn "import PhD.Main" PhD/TauCeti/` empty).
#### Mathlib lemmas needed
(none.)
#### Sources
[RM] 'Existing Lean work' (the `#print axioms` gate the roadmap asks CI to run); `plan.md` worker protocol.
#### Generality decision
n/a.

### [CLEANUP-FINAL] Run /cleanup-all on the whole layer
- **Status**: done (2026-10-06) · **Depends on**: T052 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06: final sweep = the T052 gate plus: roadmap README Layer 1 'Status (2026-10-06)' note added; `plan.md` 'Execution notes' added; board header set to COMPLETE; memory entry `tauceti-np-layer1-board` updated.
- Final sweep of the twelve files of this board (`PhD/TauCeti/Code/NewtonPolygons/AddVal/*.lean`): naming against the [PR] names and Mathlib conventions, docstrings, import minimality by hand, module docstrings list the final declaration names, `omit` of unused section instances, `runLinter` clean on every module, `lake build PhD.TauCeti` passes, `#print axioms` standard on the five milestones. Then update the Status line of this file, add a 'Status' note at the head of the roadmap README's Layer 1 section (as Layer 0 and the RigidAnalyticGeometry layers have), and the memory entry of the board.
