# Ticket board: Tau Ceti `NewtonPolygons`, Layer 2 (the polygon of a polynomial and of a power series)

**Board**: `.mathlib-quality/tauceti-np-layer2/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, `tauceti-np-layer0/` and `tauceti-np-layer1/` are the finished
Layers 0 and 1).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 2 (introduction, §2.1–§2.4, Examples) — cited
as [RM].
**Code**: `PhD/TauCeti/Code/NewtonPolygons/Coeff/` (`NormedAddValuation`, `Generic`, `CoeffVal`, `PowerSeries`,
`Polynomial`, `Extension`, `SupportValue`, `GaussNorm`, `Pure`, `Distinguished`, `Padic`, `Examples`) — 12 files,
module prefix `PhD.TauCeti.Code.NewtonPolygons.Coeff`; the chain root `PhD/TauCeti.lean` imports the leaf
`Coeff.Examples`. Planned 2026-10-06.
**Name check**: every Mathlib / Layer 0 / Layer 1 / rigid-chain name in the "Mathlib lemmas needed" blocks
elaborates against the pin (`scratch/names_tickets_mathlib.lean`) and every skeleton name
(`scratch/signatures.lean`, 0 errors); see `plan.md`, "Name check".

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 72 (`T001`–`T072`; `T072` is the chain-root gate) |
| Per-file cleanups | 28 (`CLEANUP-1`–`CLEANUP-28`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **106** |

- Open: 106 | In Progress: 0 | Done: 0.
- Coverage: every open declaration of the skeleton (256, 261 `sorry`s) is named in exactly one ticket (the
  generator `scratch/gen_tickets.py` fails otherwise).
- **Milestone M1** = `T019`: `PowerSeries.isAdmissible_coeffVal_iff_exists_isRestricted` — the polygon of a
  series exists exactly when the series is restricted at some positive radius ([RM] §2.1.3).
- **Milestone M2** = `T034`: `Polynomial.newtonPolygon_reverse` — the reflection ([RM] §2.2.7, "a milestone,
  not a remark").
- **Milestone M3** = `T049`: `PowerSeries.gaussNorm_rpow_eq_of_supportValue_eq` (with `hasGaussNorm_rpow_iff`
  from `T048`) — the Gauss norm is `b ^ (−s)`, the Legendre transform of the polygon ([RM] §2.3.1–§2.3.2).
- **Milestone M4** = `T062`: `Polynomial.HasFirstBreak.isMulDistinguished` — first break ⟹ distinguished
  ([RM] §2.4.3).
- **Milestone M5** = `T071`: `Polynomial.isPure_one_add_three_pow_mul_X_sq` and
  `Polynomial.isPure_C_inv_mul_cyclotomic_comp_X_add_one` — the acceptance examples `1 + 3^{2j+1} X²` (slope
  `j + ½`) and `Φ_p(X+1)/p` (slope `−1/(p−1)`).
- Parallel capacity: 3 at the start (`NormedAddValuation.lean` ∥ `Generic.lean` ∥ `SupportValue.lean`), 2 after
  `NormedAddValuation.lean` (`CoeffVal.lean` ∥ `Padic.lean`); on this machine run one Lean process at a time
  (other boards are active), so the honest estimate is one worker.

Conventions binding every ticket (see `plan.md`, "Generality and design decisions"): one bundle
`NormedField.NormedAddValuation K Γ` over `[NormedField K]` (no ultrametric or nontriviality instance except
in the three Layer-1 instances); radii are `v.base ^ m`; Gauss norms are `PowerSeries.gaussNorm norm c` with
polynomials through the coercion and `Polynomial.gaussNorm_toAbsoluteValue` as the only bridge; the
supporting value is an `EReal`; restrictedness is the rigid chain's `PowerSeries.IsRestricted`
(`isRestricted_iff'` along `atTop`); no `import PhD.Main.*` — the Main-chain files are read-only proof
references, cited as [SRC]. Deviations and errata D1–D10 are recorded in `plan.md` and are not to be
"fixed" by a worker; in particular §2.4.4 is deferred to Layer 3/4, not ticketed.

Worker protocol: `/beastmode` inline as the main agent (user preference); after each ticket
`lake build PhD.TauCeti.Code.NewtonPolygons.Coeff.<File>` and `#print axioms` on each declaration (only
`propext`, `Classical.choice`, `Quot.sound`); mark `done` only with zero `sorry` in the ticket's
declarations; append a `Progress` line to the ticket with a timestamp; record any statement repair in
`b2_log.jsonl`. `omega`, not `lia`, for linear `ℕ` goals.

## Dependency order (ticket groups)

```text
G1 NormedAddValuation : T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → T006 → CLEANUP-2 → T007 → T008 → T009 → CLEANUP-3
G2 Generic            : T010 → T011 → T012 → CLEANUP-4 → T013 → T014 → T015 → CLEANUP-5          (∥ G1, G7)
G3 CoeffVal           : T016 → T017 → T018 → CLEANUP-6 → CLEANUP-ALL-1 → T019 [M1] → T020 → CLEANUP-7   (after CLEANUP-3)
G4 PowerSeries        : T021 → T022 → T023 → CLEANUP-8 → T024 → T025 → T026 → CLEANUP-9 → T027 → CLEANUP-10
                                                                                     (after CLEANUP-5, CLEANUP-7)
G5 Polynomial         : T028 → T029 → T030 → CLEANUP-11 → T031 → T032 → T033 → CLEANUP-12 → CLEANUP-ALL-2
                        → T034 [M2] → T035 → T036 → CLEANUP-13                               (after CLEANUP-10)
G6 Extension          : T037 → T038 → CLEANUP-14                                            (after CLEANUP-13)
G7 SupportValue       : T039 → T040 → T041 → CLEANUP-15 → T042 → T043 → T044 → CLEANUP-16 → T045 → T046 → CLEANUP-17
                                                                                     (Layer 0 only; ∥ G1–G6)
G8 GaussNorm          : T047 → T048 → CLEANUP-ALL-3 → T049 [M3] → CLEANUP-18 → T050 → T051 → T052 → CLEANUP-19
                        → T053 → CLEANUP-20                                         (after CLEANUP-13, CLEANUP-17)
G9 Pure               : T054 → T055 → T056 → CLEANUP-21 → T057 → T058 → T059 → CLEANUP-22 → T060 → CLEANUP-23
                                                                                     (after CLEANUP-20)
G10 Distinguished     : T061 → CLEANUP-ALL-4 → T062 [M4] → CLEANUP-24                       (after CLEANUP-23)
G11 Padic             : T063 → CLEANUP-25                                                   (after CLEANUP-3; ∥ G3–G10)
G12 Examples          : T064 → T065 → T066 → CLEANUP-26 → T067 → T068 → T069 → CLEANUP-27 → T070 → CLEANUP-ALL-5
                        → T071 [M5] → CLEANUP-28                                 (after CLEANUP-14, CLEANUP-24, CLEANUP-25)
G13 gate              : T072 → CLEANUP-FINAL                                                (after every final cleanup)
```

---

## Tickets

### [T001] `NormedAddValuation`: the additive-valuation API through `CoeFun`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: none · **Parallel**: yes (with T010, T039) · **Type**: structure API
- **Leaves**: L1.1–L1.9

#### Statement
```lean
structure NormedAddValuation where
  /-- The additive valuation. -/
  toAddValuation : AddValuation K (WithTop Γ)
  /-- The real embedding of the value group. -/
  embed : Γ →+ ℝ
  /-- The embedding is strictly monotone. -/
  strictMono_embed : StrictMono embed
  /-- The base of the norm. -/
  base : ℝ
  /-- The base exceeds `1`. -/
  one_lt_base : 1 < base
  /-- The norm is the base to the power of minus the embedded valuation. -/
  norm_eq_rpow' : ∀ {x : K} {γ : Γ}, toAddValuation x = (γ : WithTop Γ) → ‖x‖ = base ^ (-embed γ)

lemma map_zero : v 0 = ⊤ := by sorry

lemma map_one : v 1 = 0 := by sorry

lemma map_mul (x y : K) : v (x * y) = v x + v y := by sorry

lemma map_pow (x : K) (n : ℕ) : v (x ^ n) = n • v x := by sorry

lemma map_inv (x : K) : v x⁻¹ = -v x := by sorry

lemma min_le_map_add (x y : K) : min (v x) (v y) ≤ v (x + y) := by sorry

@[simp] lemma eq_top_iff {x : K} : v x = ⊤ ↔ x = 0 := by sorry

lemma ne_top_iff {x : K} : v x ≠ ⊤ ↔ x ≠ 0 := by sorry

lemma exists_eq_coe {x : K} (hx : x ≠ 0) : ∃ γ : Γ, v x = (γ : WithTop Γ) := by sorry
```
#### Proof sketch
The structure is already defined (no `sorry` in it); this ticket proves the nine one-line API lemmas.
1. `map_zero` … `min_le_map_add`: `v x` unfolds to `v.toAddValuation x` by `coe_apply` (`rfl`); each lemma is
   the corresponding `AddValuation` lemma: `AddValuation.map_zero`, `map_one`, `map_mul`, `map_pow`,
   `map_inv` (`WithTop Γ` is a `LinearOrderedAddCommGroupWithTop`), `map_add`.
2. `eq_top_iff`: `AddValuation.top_iff` on the field `K` (`[Nontrivial (WithTop Γ)]` is found).
   `ne_top_iff`: `AddValuation.ne_top_iff` (or `eq_top_iff.not`).
3. `exists_eq_coe`: `WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hx)`.
Decomposition entry: L1.1–L1.9.
#### Mathlib lemmas needed
`AddValuation.map_zero`, `AddValuation.map_one`, `AddValuation.map_mul`, `AddValuation.map_pow`, `AddValuation.map_inv`, `AddValuation.map_add`, `AddValuation.top_iff`, `AddValuation.ne_top_iff`, `WithTop.ne_top_iff_exists`.
#### Sources
[RM] Layer 2 introduction (Q-RM-intro); [RM] convention 5.
#### Generality decision
`[NormedField K]` only (no ultrametric, no nontriviality instance): the structure's norm axiom forces ultrametricity (T002). `Γ` any `[AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]`; universe-polymorphic.

### [T002] The base and the norm: `norm_eq_rpow`, `embed_eq_neg_logb`, ultrametricity, `rpow_logb`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T001 · **Parallel**: yes (with T010, T039) · **Type**: lemmas
- **Leaves**: L1.10–L1.15

#### Statement
```lean
lemma base_pos : 0 < v.base := by sorry

lemma log_base_pos : 0 < Real.log v.base := by sorry

lemma norm_eq_rpow {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) :
    ‖x‖ = v.base ^ (-v.embed γ) := by sorry

lemma embed_eq_neg_logb {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) :
    v.embed γ = -Real.logb v.base ‖x‖ := by sorry

lemma norm_add_le_max (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by sorry

lemma rpow_logb {c : ℝ} (hc : 0 < c) : v.base ^ Real.logb v.base c = c := by sorry
```
#### Proof sketch
1. `base_pos := zero_lt_one.trans v.one_lt_base`; `log_base_pos := Real.log_pos v.one_lt_base`.
2. `norm_eq_rpow := v.norm_eq_rpow' h`.
3. `embed_eq_neg_logb`: from `‖x‖ = b ^ (-e γ)` take `Real.logb b` of both sides:
   `Real.logb_rpow v.base_pos v.one_lt_base.ne'` gives `logb b ‖x‖ = -e γ`; `neg_neg`.
4. `norm_add_le_max`: if `x + y = 0` the left side is `0 ≤ max _ _` (`norm_nonneg`); otherwise obtain `γ` with
   `v (x + y) = γ` (`exists_eq_coe`). If `x = 0` or `y = 0` the claim is trivial (`zero_add`, `le_max_right`).
   Else `v x = γ₁`, `v y = γ₂`, `min γ₁ γ₂ ≤ γ` (`min_le_map_add`, `WithTop.coe_le_coe`, `WithTop.coe_min`), so
   `e γ ≥ min (e γ₁) (e γ₂)` (`v.strictMono_embed.monotone`, `Monotone.map_min`), hence
   `b ^ (-e γ) ≤ max (b ^ (-e γ₁)) (b ^ (-e γ₂))` by `Real.rpow_le_rpow_left_iff v.one_lt_base` and
   `neg_le_neg`; rewrite the three norms with `norm_eq_rpow`.
5. `rpow_logb := Real.rpow_logb v.base_pos v.one_lt_base.ne' hc`.
Decomposition entry: L1.10–L1.15.
#### Mathlib lemmas needed
`zero_lt_one`, `Real.log_pos`, `Real.logb_rpow`, `Real.rpow_logb`, `Real.rpow_le_rpow_left_iff`, `WithTop.coe_le_coe`, `WithTop.coe_min`, `Monotone.map_min`, `StrictMono.monotone`, `norm_nonneg`, `le_max_left`, `le_max_right`, `neg_le_neg`, `neg_neg`.
#### Sources
[RM] Layer 2 introduction; [RM] convention 2 ("e (v x) … equal -log ‖x‖"); Layer 1's [BGR] 1.5.2 dictionary.
#### Generality decision
As T001. `norm_add_le_max` is a theorem about the bundle, so the layer never assumes `IsUltrametricDist K` (plan decision 1).

### [T003] `embedTop`: pushing `WithTop Γ` into `WithTop ℝ`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T002 · **Parallel**: yes (with T010, T039) · **Type**: def API
- **Leaves**: L1.16–L1.23

#### Statement
```lean
def embedTop : WithTop Γ → WithTop ℝ := WithTop.map v.embed

@[simp] lemma embedTop_top : v.embedTop ⊤ = ⊤ := by sorry

@[simp] lemma embedTop_coe (γ : Γ) : v.embedTop (γ : WithTop Γ) = (v.embed γ : WithTop ℝ) := by sorry

lemma embedTop_eq_top_iff {a : WithTop Γ} : v.embedTop a = ⊤ ↔ a = ⊤ := by sorry

lemma embedTop_strictMono : StrictMono v.embedTop := by sorry

lemma embedTop_le_embedTop {a b : WithTop Γ} : v.embedTop a ≤ v.embedTop b ↔ a ≤ b := by sorry

lemma embedTop_add (a b : WithTop Γ) : v.embedTop (a + b) = v.embedTop a + v.embedTop b := by sorry

lemma embedTop_apply_eq_top_iff {x : K} : v.embedTop (v x) = ⊤ ↔ x = 0 := by sorry

lemma embedTop_map_one : v.embedTop (v 1) = 0 := by sorry
```
#### Proof sketch
`embedTop = WithTop.map v.embed` (no `sorry` in the definition).
1. `embedTop_top := WithTop.map_top _`; `embedTop_coe := WithTop.map_coe _ _`; `embedTop_eq_top_iff := WithTop.map_eq_top_iff`.
2. `embedTop_strictMono := WithTop.strictMono_map_iff.mpr v.strictMono_embed`;
   `embedTop_le_embedTop := v.embedTop_strictMono.le_iff_le`.
3. `embedTop_add := WithTop.map_add v.embed a b` (`Γ →+ ℝ` is an `AddHomClass`).
4. `embedTop_apply_eq_top_iff`: `embedTop_eq_top_iff.trans v.eq_top_iff`.
5. `embedTop_map_one`: `rw [v.map_one]`, then `embedTop_coe`, `map_zero`, `WithTop.coe_zero`.
Decomposition entry: L1.16–L1.23.
#### Mathlib lemmas needed
`WithTop.map_top`, `WithTop.map_coe`, `WithTop.map_eq_top_iff`, `WithTop.strictMono_map_iff`, `StrictMono.le_iff_le`, `WithTop.map_add`, `map_zero`, `WithTop.coe_zero`.
#### Sources
[RM] convention 4 ("The points live in WithTop Γ, pushed into WithTop ℝ along e").
#### Generality decision
As T001; `embedTop` is stated on all of `WithTop Γ`, not only on values of `v`.

### [CLEANUP-1] Run /cleanup on `NormedAddValuation.lean`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T004] The term dictionary against `1`: `‖x‖ (b^m)^k ≤ 1`, `< 1`, `= 1`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: CLEANUP-1 · **Parallel**: yes (with T010, T039) · **Type**: lemmas
- **Leaves**: L1.24–L1.27

#### Statement
```lean
theorem norm_mul_rpow_pow_eq_rpow {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = v.base ^ (m * k - v.embed γ) := by sorry

theorem norm_mul_rpow_pow_le_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k ≤ 1 ↔ ((m * k : ℝ) : WithTop ℝ) ≤ v.embedTop (v x) := by sorry

theorem norm_mul_rpow_pow_lt_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k < 1 ↔ ((m * k : ℝ) : WithTop ℝ) < v.embedTop (v x) := by sorry

theorem norm_mul_rpow_pow_eq_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = 1 ↔ v.embedTop (v x) = ((m * k : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `norm_mul_rpow_pow_eq_rpow`: rewrite `‖x‖` by `norm_eq_rpow h`; `(b ^ m) ^ k = b ^ (m * k)` by
   `← Real.rpow_natCast, ← Real.rpow_mul v.base_pos.le`; `b ^ (-eγ) * b ^ (mk) = b ^ (-eγ + mk)` by
   `← Real.rpow_add v.base_pos`; `ring_nf` for `-eγ + mk = mk - eγ`.
2. `_le_one_iff`: `rcases eq_or_ne x 0`. If `x = 0`: LHS `0 ≤ 1` (`norm_zero`, `zero_mul`, `zero_le_one`), RHS
   `_ ≤ ⊤` (`v.map_zero`, `embedTop_top`, `le_top`): both true. Else obtain `γ` (`exists_eq_coe`), rewrite with
   step 1 and `embedTop_coe`; `1 = b ^ (0:ℝ)` (`Real.rpow_zero`), `Real.rpow_le_rpow_left_iff v.one_lt_base`,
   `sub_nonpos`, `WithTop.coe_le_coe`.
3. `_lt_one_iff`: same with `Real.rpow_lt_rpow_left_iff`, `sub_neg`, `WithTop.coe_lt_coe`; `x = 0`: `0 < 1` and
   `↑(mk) < ⊤` (`WithTop.coe_lt_top`).
4. `_eq_one_iff`: `x = 0`: `0 = 1` false (`zero_ne_one`), `⊤ = ↑_` false (`WithTop.top_ne_coe`); else
   `le_antisymm_iff` on both sides with steps 2–3, or `Real.rpow_right_inj`-style via
   `(Real.rpow_le_rpow_left_iff _).antisymm_iff`; the real statement is `mk - eγ = 0 ↔ eγ = mk` (`sub_eq_zero`,
   `eq_comm`), then `WithTop.coe_inj`.
Decomposition entry: L1.24–L1.27. [SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`. ([SRC] `CoeffVal.norm_mul_exp_pow_le_one_iff` and siblings are the `b = exp 1` case.)
#### Mathlib lemmas needed
`Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_zero`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `norm_zero`, `zero_mul`, `zero_le_one`, `le_top`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`, `WithTop.coe_lt_top`, `WithTop.coe_inj`, `WithTop.top_ne_coe`, `sub_nonpos`, `sub_neg`, `sub_eq_zero`, `le_antisymm_iff`.
#### Sources
[RM] §2.1.2 (Q-RM-2.1.2); [Gou20] §7.4 p. 254 (Q-Gou-first: "|a_j|(p^m)^j ≤ 1 for all j … = 1 … < 1").
#### Generality decision
Stated for every `x : K` (no nonvanishing hypothesis): the `⊤` bookkeeping is the content ([RM] "the later layers use every direction of it"). `m` is any real, `k` any natural.

### [T005] The term dictionary between two terms
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T004 · **Parallel**: yes (with T010, T039) · **Type**: lemmas
- **Leaves**: L1.28–L1.30

#### Statement
```lean
theorem norm_mul_rpow_pow_le_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k ≤ ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) ≤ v.embedTop (v x) := by sorry

theorem norm_mul_rpow_pow_lt_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k < ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) < v.embedTop (v x) := by sorry

theorem norm_mul_rpow_pow_eq_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v x) = v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `_le_iff`: `rcases eq_or_ne y 0` then `rcases eq_or_ne x 0`.
   - `y = 0`: LHS `‖x‖ (b^m)^k ≤ 0 ↔ x = 0` (`mul_nonpos_iff`-free: `(mul_pos (norm_pos_iff.mpr hx) (pow_pos (Real.rpow_pos_of_pos _ _) _)).not_le` for `x ≠ 0`; `le_refl` for `x = 0`); RHS `⊤ + _ ≤ embedTop (v x) ↔ embedTop (v x) = ⊤ ↔ x = 0` (`WithTop.top_add`, `top_le_iff`, `embedTop_apply_eq_top_iff`).
   - `x = 0, y ≠ 0`: both sides true (`norm_zero`, `zero_mul`, `mul_nonneg`; `le_top`).
   - both nonzero: `norm_mul_rpow_pow_eq_rpow` twice, `embedTop_coe` twice, `WithTop.coe_add`, `WithTop.coe_le_coe`, `Real.rpow_le_rpow_left_iff v.one_lt_base`; the real inequality `mk - eγ ≤ mj - eγ' ↔ eγ' + m (k - j) ≤ eγ` is `linarith`/`ring_nf` (`mul_sub`).
2. `_lt_iff`: same case split with `Real.rpow_lt_rpow_left_iff`, `WithTop.coe_lt_coe`; `y = 0`: both false (`not_lt.mpr (mul_nonneg …)`, `not_top_lt`); `x = 0 ≠ y`: both true (`mul_pos`, `WithTop.coe_lt_top`).
3. `_eq_iff`: `x = y = 0` both true (`WithTop.top_add`); exactly one zero: both false (`WithTop.top_ne_coe`, `WithTop.coe_ne_top`, `mul_pos … |>.ne'`); both nonzero: `le_antisymm_iff` and steps of 1, or directly `Real.rpow_left_injective`-free: injectivity of `t ↦ b ^ t` from `Real.rpow_lt_rpow_left_iff` (`lt_irrefl`); the real identity `mk - eγ = mj - eγ' ↔ eγ = eγ' + m (k - j)` by `linarith` both ways.
Decomposition entry: L1.28–L1.30.
#### Mathlib lemmas needed
`Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `Real.rpow_pos_of_pos`, `norm_pos_iff`, `pow_pos`, `mul_pos`, `mul_nonneg`, `norm_zero`, `zero_mul`, `WithTop.top_add`, `WithTop.coe_add`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`, `WithTop.coe_lt_top`, `WithTop.top_ne_coe`, `WithTop.coe_ne_top`, `top_le_iff`, `not_top_lt`, `le_top`, `le_antisymm_iff`, `mul_sub`.
#### Sources
[RM] §2.1.2 ("for comparison against another term rather than against 1"); [Gou20] pp. 258–259 (Q-Gou-second).
#### Generality decision
As T004; `j` and `k` arbitrary naturals, `x y` arbitrary elements.

### [T006] Two bundles on the same field differ by `scale`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T005 · **Parallel**: yes (with T010, T039) · **Type**: def API
- **Leaves**: L1.31–L1.33

#### Statement
```lean
noncomputable def scale (w : NormedAddValuation K Γ') : ℝ := Real.log v.base / Real.log w.base

lemma scale_pos (w : NormedAddValuation K Γ') : 0 < v.scale w := by sorry

theorem embed_eq_scale_mul_embed (w : NormedAddValuation K Γ') {x : K} {γ : Γ} {γ' : Γ'}
    (hv : v x = (γ : WithTop Γ)) (hw : w x = (γ' : WithTop Γ')) :
    w.embed γ' = v.scale w * v.embed γ := by sorry

theorem embedTop_apply_eq_map (w : NormedAddValuation K Γ') (x : K) :
    w.embedTop (w x) = WithTop.map (fun t : ℝ ↦ v.scale w * t) (v.embedTop (v x)) := by sorry
```
#### Proof sketch
`scale v w = Real.log v.base / Real.log w.base` (no `sorry`).
1. `scale_pos := div_pos v.log_base_pos w.log_base_pos`.
2. `embed_eq_scale_mul_embed`: `‖x‖ = b ^ (-e γ)` (`v.norm_eq_rpow hv`) and `‖x‖ = b' ^ (-e' γ')` (`w.norm_eq_rpow hw`); apply `Real.log` to the equality of the right sides: `Real.log_rpow v.base_pos`, `Real.log_rpow w.base_pos` give `(-e γ) * log b = (-e' γ') * log b'`; solve for `e' γ'` with `field_simp [v.log_base_pos.ne', w.log_base_pos.ne']` and `ring` (unfold `scale`).
3. `embedTop_apply_eq_map`: `rcases eq_or_ne x 0`: `x = 0` gives `⊤ = WithTop.map _ ⊤` (`map_zero`, `embedTop_top`, `WithTop.map_top`); else obtain `γ`, `γ'` (`exists_eq_coe` for `v` and `w`), rewrite `embedTop_coe`, `WithTop.map_coe`, and step 2.
Decomposition entry: L1.31–L1.33.
#### Mathlib lemmas needed
`div_pos`, `Real.log_rpow`, `WithTop.map_top`, `WithTop.map_coe`.
#### Sources
[RM] §2.2.8 (Q-RM-2.2.8); plan D9 for the direction of the scalar (`e'(v' x) = (log b / log b') · e(v x)`).
#### Generality decision
`Γ` and `Γ'` independent ordered groups; the scalar depends only on the two bases.

### [CLEANUP-2] Run /cleanup on `NormedAddValuation.lean`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T007] The real instance `ofNormAddVal`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with T010, T039) · **Type**: def fields + lemma
- **Leaves**: L1.34–L1.35

#### Statement
```lean
noncomputable def ofNormAddVal : NormedAddValuation K ℝ where
  toAddValuation := normAddVal K
  embed := AddMonoidHom.id ℝ
  strictMono_embed := strictMono_id
  base := Real.exp 1
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

lemma ofNormAddVal_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    ofNormAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `one_lt_base`: `Real.one_lt_exp_iff.mpr zero_lt_one`.
2. `norm_eq_rpow'`: from `normAddVal K x = ↑γ`, `x ≠ 0` by `NormedField.normAddVal_eq_top` (the value is not `⊤`); `NormedField.normAddVal_apply_of_ne_zero K hx` and `WithTop.coe_inj` give `γ = -Real.log ‖x‖`; then `(Real.exp 1) ^ (-γ) = Real.exp (-γ)` (`Real.exp_one_rpow`) `= Real.exp (Real.log ‖x‖) = ‖x‖` (`neg_neg`, `Real.exp_log (norm_pos_iff.mpr hx)`).
3. `ofNormAddVal_apply_of_ne_zero := NormedField.normAddVal_apply_of_ne_zero K hx` (the coercion is `rfl`).
Decomposition entry: L1.34–L1.35.
#### Mathlib lemmas needed
`Real.one_lt_exp_iff`, `NormedField.normAddVal_eq_top`, `NormedField.normAddVal_apply_of_ne_zero`, `WithTop.coe_inj`, `Real.exp_one_rpow`, `Real.exp_log`, `norm_pos_iff`, `neg_neg`.
#### Sources
[RM] Layer 2 introduction ("(normAddVal K, id, exp 1) always"); [RM] §1.2.2–§1.2.3.
#### Generality decision
`[NontriviallyNormedField K] [IsUltrametricDist K]`, Layer 1's hypotheses for `normAddVal`.

### [T008] The discrete instance `ofNormAddValZ`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T007 · **Parallel**: yes (with T010, T039) · **Type**: def fields + lemmas
- **Leaves**: L1.36–L1.38

#### Statement
```lean
noncomputable def ofNormAddValZ {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    NormedAddValuation K ℤ where
  toAddValuation := normAddValZ K
  embed := Int.castAddHom ℝ
  strictMono_embed := by sorry
  base := ‖π‖⁻¹
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

lemma ofNormAddValZ_apply_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    ofNormAddValZ K hπ π = 1 := by sorry

lemma scale_ofNormAddValZ_ofNormAddVal {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    (ofNormAddValZ K hπ).scale (ofNormAddVal K) = -Real.log ‖π‖ := by sorry
```
#### Proof sketch
1. `strictMono_embed := Int.cast_strictMono` (coerced `Int.castAddHom ℝ`; `Int.coe_castAddHom`).
2. `one_lt_base`: `one_lt_inv_iff₀.mpr ⟨hπ0, hπ1⟩` with `0 < ‖π‖` and `‖π‖ < 1`: `hπ : IsUniformizer _ π` means `valuation π = ↑(generator _)` (`Valuation.IsUniformizer.iff`), `NormedField.valuation_apply` reads `‖π‖₊ = generator`, `Valuation.IsRankOneDiscrete.generator_lt_one` gives `‖π‖₊ < 1` (`Units.val_lt_one`-style coercions) and `generator ≠ 0` (`Units.ne_zero`) gives `‖π‖₊ ≠ 0`; pass to `ℝ` with `NNReal.coe_lt_coe`, `NNReal.coe_pos`, `coe_nnnorm`.
3. `norm_eq_rpow'`: from `normAddValZ K x = ↑d`, `NormedField.normAddValZ_eq_iff_of_isUniformizer K hπ x d` gives `‖x‖ = ‖π‖ ^ d` (`zpow`); rewrite `(‖π‖⁻¹) ^ (-(d:ℝ)) = (‖π‖⁻¹) ^ (-d : ℤ)` (`Real.rpow_intCast` after `Int.cast_neg`) `= ‖π‖ ^ d` (`inv_zpow'`, `zpow_neg`, `inv_inv`).
4. `ofNormAddValZ_apply_isUniformizer := NormedField.normAddValZ_isUniformizer K hπ`.
5. `scale_ofNormAddValZ_ofNormAddVal`: unfold `scale`, `ofNormAddValZ_base`, `ofNormAddVal_base`; `Real.log_inv`, `Real.log_exp`, `div_one`.
Decomposition entry: L1.36–L1.38.
#### Mathlib lemmas needed
`Int.cast_strictMono`, `Int.coe_castAddHom`, `one_lt_inv_iff₀`, `Valuation.IsUniformizer.iff`, `NormedField.valuation_apply`, `Valuation.IsRankOneDiscrete.generator_lt_one`, `Units.ne_zero`, `NNReal.coe_lt_coe`, `NNReal.coe_pos`, `coe_nnnorm`, `NormedField.normAddValZ_eq_iff_of_isUniformizer`, `Real.rpow_intCast`, `Int.cast_neg`, `inv_zpow'`, `zpow_neg`, `inv_inv`, `NormedField.normAddValZ_isUniformizer`, `Real.log_inv`, `Real.log_exp`, `div_one`.
#### Sources
[RM] Layer 2 introduction ("(normAddValZ K, Int.cast, ‖π‖⁻¹) for a discretely valued K with uniformiser π"); [RM] §1.3.2, §1.3.4; §2.2.8 ("divided by log p").
#### Generality decision
`[(valuation (K := K)).IsRankOneDiscrete]` as an instance, the uniformiser as an explicit hypothesis `hπ` (Layer 1's shape).

### [T009] The rational instance `ofNormAddValQ`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T008 · **Parallel**: yes (with T010, T039) · **Type**: def fields + lemma
- **Leaves**: L1.39–L1.40

#### Statement
```lean
noncomputable def ofNormAddValQ : NormedAddValuation K ℚ where
  toAddValuation := normAddValQ K π
  embed := (Rat.castHom ℝ).toAddMonoidHom
  strictMono_embed := by sorry
  base := ‖π‖⁻¹
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

lemma ofNormAddValQ_self : ofNormAddValQ K π π = 1 := by sorry
```
#### Proof sketch
1. `strictMono_embed := Rat.cast_strictMono` (`Rat.coe_castHom`).
2. `one_lt_base`: `one_lt_inv_iff₀.mpr ⟨_, _⟩` from `Valuation.IsCommensurable.val_pos` (`0 < valuation π`, i.e. `0 < ‖π‖₊`, `NormedField.valuation_apply`) and `Valuation.IsCommensurable.val_lt_one` (`‖π‖₊ < 1`), coerced to `ℝ`.
3. `norm_eq_rpow'`: from `normAddValQ K π x = ↑q`, `NormedField.norm_eq_norm_rpow_normAddValQ K π hq : ‖x‖ = ‖π‖ ^ (q:ℝ)`; `(‖π‖⁻¹) ^ (-(q:ℝ)) = (‖π‖ ^ (q:ℝ))⁻¹⁻¹`: `Real.inv_rpow (norm_nonneg _)`, `Real.rpow_neg (norm_nonneg _)`, `inv_inv`.
4. `ofNormAddValQ_self := NormedField.normAddValQ_self K π`.
Decomposition entry: L1.39–L1.40.
#### Mathlib lemmas needed
`Rat.cast_strictMono`, `Rat.coe_castHom`, `one_lt_inv_iff₀`, `Valuation.IsCommensurable.val_pos`, `Valuation.IsCommensurable.val_lt_one`, `NormedField.valuation_apply`, `NormedField.norm_eq_norm_rpow_normAddValQ`, `Real.inv_rpow`, `Real.rpow_neg`, `inv_inv`, `norm_nonneg`, `NormedField.normAddValQ_self`.
#### Sources
[RM] Layer 2 introduction ("(normAddValQ K π, Rat.cast, ‖π‖⁻¹) in the commensurable case"); [RM] §1.4.6.
#### Generality decision
`π` explicit with `[(valuation (K := K)).IsCommensurable π]` (convention 3: normalisation by an element).

### [CLEANUP-3] Run /cleanup on `NormedAddValuation.lean`
- **Status**: open · **File**: `NormedAddValuation.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T010] Finite support is admissible; `shiftRight` basics
- **Status**: open · **File**: `Generic.lean` · **Depends on**: none · **Parallel**: yes (with T001, T039) · **Type**: def API
- **Leaves**: L2.1–L2.6

#### Statement
```lean
def shiftRight (n : ℕ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if n ≤ k then v (k - n) else ⊤

theorem isAdmissible_of_finite (hfin : (finiteSupport v).Finite) : IsAdmissible v := by sorry

@[simp] theorem shiftRight_add (n : ℕ) (v : ℕ → WithTop ℝ) (k : ℕ) :
    shiftRight n v (k + n) = v k := by sorry

theorem shiftRight_of_le {n k : ℕ} (hk : n ≤ k) (v : ℕ → WithTop ℝ) :
    shiftRight n v k = v (k - n) := by sorry

theorem shiftRight_of_lt {n k : ℕ} (hk : k < n) (v : ℕ → WithTop ℝ) : shiftRight n v k = ⊤ := by sorry

@[simp] theorem shiftRight_zero (v : ℕ → WithTop ℝ) : shiftRight 0 v = v := by sorry

theorem unitSlope_shiftRight (n : ℕ) (h : ℕ → WithTop ℝ) (k : ℕ) :
    unitSlope (shiftRight n h) (k + n) = unitSlope h k := by sorry
```
#### Proof sketch
1. `isAdmissible_of_finite`: the image `(fun k ↦ (v k).untop₀) '' finiteSupport v` is finite (`Set.Finite.image`), hence bounded below (`Set.Finite.bddBelow`); with `y` a lower bound apply `NewtonPolygon.isAdmissible_of_line (y := y) (σ := 0)`: for `v k = ⊤` the inequality is `le_top`; for `v k ≠ ⊤`, `y + 0 * k = y ≤ (v k).untop₀` and `WithTop.coe_untop₀_of_ne_top` (`WithTop.coe_le_coe`).
2. `shiftRight_add`: `simp [shiftRight, Nat.le_add_left]` (`Nat.add_sub_cancel`). `shiftRight_of_le`: `if_pos hk`. `shiftRight_of_lt`: `if_neg (not_le.mpr hk)`. `shiftRight_zero`: `funext`, `if_pos (zero_le _)`, `Nat.sub_zero`.
3. `unitSlope_shiftRight`: `unitSlope_nat` twice; `k + n + 1 = (k + 1) + n` (`Nat.add_right_comm`) and `shiftRight_add` twice.
Decomposition entry: L2.1–L2.6.
#### Mathlib lemmas needed
`Set.Finite.image`, `Set.Finite.bddBelow`, `WithTop.coe_untop₀_of_ne_top`, `WithTop.coe_le_coe`, `le_top`, `Nat.le_add_left`, `Nat.add_sub_cancel`, `Nat.add_right_comm`, `Nat.sub_zero`, `zero_le`, `if_pos`, `if_neg`, `not_le`, `funext`.
#### Sources
[RM] §0.2.3 ("it holds for every sequence on or above a single line"), §2.1.3, §2.2.7 ("the polygon of X^n · f is translated right by n").
#### Generality decision
Generic over `v : ℕ → WithTop ℝ` (namespace `NewtonPolygon`); Tau Ceti home Layer 0's `Basic.lean`.

### [T011] The shifted polygon is the shifted sequence's polygon
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T010 · **Parallel**: yes (with T001, T039) · **Type**: theorems
- **Leaves**: L2.7–L2.10

#### Statement
```lean
theorem isConvexSeq_shiftRight_iff (n : ℕ) : IsConvexSeq (shiftRight n h) ↔ IsConvexSeq h := by sorry

theorem isNewtonPolygonOf_shiftRight_iff (n : ℕ) :
    IsNewtonPolygonOf (shiftRight n v) (shiftRight n h) ↔ IsNewtonPolygonOf v h := by sorry

theorem isAdmissible_shiftRight_iff (n : ℕ) : IsAdmissible (shiftRight n v) ↔ IsAdmissible v := by sorry

theorem newtonPolygon_shiftRight (hv : IsAdmissible v) (n : ℕ) :
    newtonPolygon (shiftRight n v) = shiftRight n (newtonPolygon v) := by sorry
```
#### Proof sketch
1. `isConvexSeq_shiftRight_iff`: use `NewtonPolygon.isConvexSeq_iff_midpoint` on both sides. Midpoint: for `k + 2 < n`, `k + 1 < n` or `k + 2 = n`… case on `n ≤ k`: then all three indices are `≥ n` and the inequality is the original one at `k - n` (`shiftRight_of_le`, `Nat.sub_add_comm`); if `k < n` the right side contains `⊤` (`shiftRight_of_lt`, `WithTop.top_add`/`WithTop.add_top`, `le_top`). Order-connectedness: `finiteSupport (shiftRight n h) = (· + n) '' finiteSupport h` (`Set.ext`, `mem_finiteSupport`, `shiftRight_of_le`/`_of_lt`); an image of an interval under `· + n` is an interval (`Set.OrdConnected` unfolded: for `a + n ≤ x ≤ b + n`, `x = (x - n) + n` with `a ≤ x - n ≤ b`), and conversely the preimage.
2. `isNewtonPolygonOf_shiftRight_iff`: `constructor` on the three fields.
   (→) `convex` by 1; `le_points k`: for `n ≤ k` it is the given one at `k - n` via `shiftRight_of_le`, else `le_top`; `greatest g hg hgv k`: `shiftRight n g` is convex (1) and `≤ shiftRight n v`, so `shiftRight n g (k + n) ≤ shiftRight n h (k + n)` (`shiftRight_add`).
   (←) `convex` by 1; `le_points` by cases; `greatest g hg hgv k`: let `g' := fun k ↦ g (k + n)`; `g'` convex (`isConvexSeq_iff_midpoint` transports: midpoint at `k` is `g`'s at `k + n`; order-connectedness of a preimage under `· + n`), `g' ≤ v` (from `hgv (k + n)` and `shiftRight_add`), so `g' ≤ h`; for `n ≤ k` write `k = (k - n) + n`, `g k = g' (k - n) ≤ h (k - n) = shiftRight n h k`; for `k < n`, `shiftRight n h k = ⊤`.
3. `isAdmissible_shiftRight_iff`: `isAdmissible_iff_exists_line` both sides; given `y + σ k ≤ v k` take `(y - σ n) + σ k ≤ shiftRight n v k` (for `k ≥ n`: `(y - σn) + σk = y + σ(k - n)`, `Nat.cast_sub`; for `k < n`: `le_top`); conversely given a line below the shift, read it at `k + n` (`shiftRight_add`, `Nat.cast_add`, `ring_nf`).
4. `newtonPolygon_shiftRight`: `(isNewtonPolygonOf_shiftRight_iff n).mpr (isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.mpr hv))` then `IsNewtonPolygonOf.eq_newtonPolygon`.
Decomposition entry: L2.7–L2.10.
#### Mathlib lemmas needed
`NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.mem_finiteSupport`, `NewtonPolygon.isAdmissible_iff_exists_line`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Set.OrdConnected`, `WithTop.top_add`, `WithTop.add_top`, `le_top`, `Nat.sub_add_comm`, `Nat.cast_sub`, `Nat.cast_add`, `Nat.sub_add_cancel`.
#### Sources
[RM] §2.2.7 ("translated right by n"); §0.2.4 ("phrased with newtonPolygon and its characterisation, never with the construction").
#### Generality decision
Generic; the `iff` forms need no admissibility, only the final `newtonPolygon_shiftRight` does.

### [T012] `reflect` basics and its unit slopes
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T011 · **Parallel**: yes (with T001, T039) · **Type**: def API
- **Leaves**: L2.11–L2.14

#### Statement
```lean
def reflect (d : ℕ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if k ≤ d then v (d - k) else ⊤

theorem reflect_of_le {d k : ℕ} (hk : k ≤ d) (v : ℕ → WithTop ℝ) : reflect d v k = v (d - k) := by sorry

theorem reflect_of_lt {d k : ℕ} (hk : d < k) (v : ℕ → WithTop ℝ) : reflect d v k = ⊤ := by sorry

theorem reflect_reflect {d : ℕ} (hv : ∀ k, d < k → v k = ⊤) : reflect d (reflect d v) = v := by sorry

theorem unitSlope_reflect {d k : ℕ} (hk : k < d) (h : ℕ → WithTop ℝ) :
    unitSlope (reflect d h) k = -unitSlope h (d - (k + 1)) := by sorry
```
#### Proof sketch
1. `reflect_of_le := if_pos hk`; `reflect_of_lt := if_neg (not_le.mpr hk)`.
2. `reflect_reflect`: `funext k`; if `k ≤ d`: `reflect_of_le`, `Nat.sub_le`, `Nat.sub_sub_self hk`; else both `⊤` (`reflect_of_lt`, `hv k hk`).
3. `unitSlope_reflect`: `unitSlope_nat` twice, `reflect_of_le` at `k + 1 ≤ d` and `k ≤ d`; `d - k = (d - (k+1)) + 1` (`omega`); then a case analysis on `h (d - (k+1))` and `h (d - k)` being `⊤` (`WithTop.ne_top_iff_exists`): finite–finite is `LinearOrderedAddCommGroup.coe_sub`, `coe_neg`, `neg_sub`; any `⊤` gives `⊤` on both sides (`LinearOrderedAddCommGroup.top_sub`, `sub_top`, `neg_top`).
Decomposition entry: L2.11–L2.14.
#### Mathlib lemmas needed
`if_pos`, `if_neg`, `not_le`, `Nat.sub_le`, `Nat.sub_sub_self`, `NewtonPolygon.unitSlope_nat`, `WithTop.ne_top_iff_exists`, `WithTop.LinearOrderedAddCommGroup.coe_sub`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `WithTop.LinearOrderedAddCommGroup.top_sub`, `WithTop.LinearOrderedAddCommGroup.sub_top`, `WithTop.LinearOrderedAddCommGroup.neg_top`, `neg_sub`.
#### Sources
[RM] §2.2.7 ("the polygon of Polynomial.reverse f is the reflection i ↦ h (d - i)").
#### Generality decision
Generic; `reflect d` is total, with `⊤` beyond `d`.

### [CLEANUP-4] Run /cleanup on `Generic.lean`
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T013] The reflected polygon is the reflected sequence's polygon
- **Status**: open · **File**: `Generic.lean` · **Depends on**: CLEANUP-4 · **Parallel**: yes (with T001, T039) · **Type**: theorems
- **Leaves**: L2.15–L2.17

#### Statement
```lean
theorem IsConvexSeq.reflect (hh : IsConvexSeq h) {d : ℕ} (hd : ∀ k, d < k → h k = ⊤) :
    IsConvexSeq (reflect d h) := by sorry

theorem IsNewtonPolygonOf.reflect (hh : IsNewtonPolygonOf v h) {d : ℕ}
    (hv : ∀ k, d < k → v k = ⊤) : IsNewtonPolygonOf (reflect d v) (reflect d h) := by sorry

theorem newtonPolygon_reflect {d : ℕ} (hv : ∀ k, d < k → v k = ⊤) :
    newtonPolygon (reflect d v) = reflect d (newtonPolygon v) := by sorry
```
#### Proof sketch
1. `IsConvexSeq.reflect`: `isConvexSeq_iff_midpoint`. Midpoint at `k`: if `k + 2 ≤ d`, the three reflected values are `h (d-k)`, `h (d-k-1)`, `h (d-k-2)` and the inequality is `hh`'s midpoint at `d - (k+2)` with the two outer terms swapped (`add_comm`); if `k + 1 ≥ d`… cases `k + 2 > d`: the right side has a `⊤` (`reflect_of_lt`) — `le_top` after `WithTop.add_top`. Order-connectedness: `finiteSupport (reflect d h) = {k | k ≤ d ∧ h (d - k) ≠ ⊤}`; for `a ≤ x ≤ b` in it, `d - b ≤ d - x ≤ d - a` (`Nat.sub_le_sub_left`) and `hh.ordConnected.out` gives `h (d - x) ≠ ⊤`; `x ≤ b ≤ d`.
2. `IsNewtonPolygonOf.reflect`: `hd : ∀ k, d < k → h k = ⊤` from `hv` and `hh.le_points` (`top_le_iff`). `convex` by 1. `le_points k`: `reflect_of_le`/`reflect_of_lt` and `hh.le_points (d - k)`. `greatest g hg hgv k`: let `g₀ := (Set.Iic d).piecewise g ⊤` (`g` on `[0, d]`, `⊤` beyond), convex by `IsConvexSeq.piecewise_top hg Set.ordConnected_Iic`, and `g' := reflect d g₀` (equal to `reflect d g` pointwise since both read `g (d - k)` for `k ≤ d`); `g'` is convex by 1 (with `g₀ = ⊤` beyond `d`); `g' ≤ v`: for `k ≤ d`, `g (d - k) ≤ reflect d v (d - k) = v k` (`hgv`, `reflect_of_le`, `Nat.sub_sub_self`); for `k > d`, `⊤ ≤ v k` by `hv`. Hence `g' ≤ h` (`hh.greatest`), and for `k ≤ d`, `g k = g' (d - k) ≤ h (d - k) = reflect d h k`; for `k > d`, `reflect d h k = ⊤`.
3. `newtonPolygon_reflect`: `finiteSupport v ⊆ Set.Iic d` (`hv`), finite (`Set.finite_Iic`, `Set.Finite.subset`), so `isAdmissible_of_finite`, `isNewtonPolygonOf_newtonPolygon` (via `exists_isConvexMinorant_iff_isAdmissible`), `IsNewtonPolygonOf.reflect`, `eq_newtonPolygon`.
Decomposition entry: L2.15–L2.17 (the competitor-beyond-`d` attack and its repair are recorded there).
#### Mathlib lemmas needed
`NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `Set.ordConnected_Iic`, `NewtonPolygon.IsConvexSeq.ordConnected`, `Set.OrdConnected.out`, `Nat.sub_le_sub_left`, `Nat.sub_sub_self`, `top_le_iff`, `WithTop.add_top`, `le_top`, `Set.finite_Iic`, `Set.Finite.subset`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Set.piecewise`.
#### Sources
[RM] §2.2.7 ("⚠ The reflection … is a milestone, not a remark"); [RM] §0.2.4.
#### Generality decision
For sequences supported in `[0, d]` (`hv`), which is what `Polynomial.reverse` needs; `d` arbitrary.

### [T014] `scaleHeight`: the polygon of a height-scaled sequence
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T013 · **Parallel**: yes (with T001, T039) · **Type**: def API + theorems
- **Leaves**: L2.18–L2.25

#### Statement
```lean
def scaleHeight (c : ℝ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ WithTop.map (fun t : ℝ ↦ c * t) (v k)

theorem scaleHeight_eq_top_iff (c : ℝ) {k : ℕ} : scaleHeight c v k = ⊤ ↔ v k = ⊤ := by sorry

theorem finiteSupport_scaleHeight (c : ℝ) : finiteSupport (scaleHeight c v) = finiteSupport v := by sorry

theorem unitSlope_scaleHeight (c : ℝ) (h : ℕ → WithTop ℝ) (k : ℕ) :
    unitSlope (scaleHeight c h) k = WithTop.map (fun t : ℝ ↦ c * t) (unitSlope h k) := by sorry

theorem isConvexSeq_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsConvexSeq (scaleHeight c h) ↔ IsConvexSeq h := by sorry

theorem isNewtonPolygonOf_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsNewtonPolygonOf (scaleHeight c v) (scaleHeight c h) ↔ IsNewtonPolygonOf v h := by sorry

theorem isAdmissible_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsAdmissible (scaleHeight c v) ↔ IsAdmissible v := by sorry

theorem newtonPolygon_scaleHeight {c : ℝ} (hc : 0 < c) (hv : IsAdmissible v) :
    newtonPolygon (scaleHeight c v) = scaleHeight c (newtonPolygon v) := by sorry

theorem slopeMultiset_scaleHeight {c : ℝ} (hc : 0 < c) (hfin : (slopeIndices h).Finite) :
    slopeMultiset (scaleHeight c h) = (slopeMultiset h).map (fun t : ℝ ↦ c * t) := by sorry
```
#### Proof sketch
1. `scaleHeight_eq_top_iff := WithTop.map_eq_top_iff`; `finiteSupport_scaleHeight`: `Set.ext`, `mem_finiteSupport`, 1.
2. `unitSlope_scaleHeight`: `unitSlope_nat`; cases on `h k`, `h (k+1)` (`WithTop.ne_top_iff_exists`): `WithTop.map_coe`, `LinearOrderedAddCommGroup.coe_sub`, `mul_sub`; `⊤` cases by `WithTop.map_top`, `top_sub`, `sub_top`.
3. `isConvexSeq_scaleHeight_iff (hc : 0 < c)`: unfold `IsConvexSeq`; order-connectedness by 1; `MonotoneOn (unitSlope (scaleHeight c h))` ↔ `MonotoneOn (unitSlope h)` by 2 and the order embedding `WithTop.map (c * ·)` (`WithTop.strictMono_map_iff.mpr (strictMono_mul_left_of_pos hc)`, `.le_iff_le`).
4. `isNewtonPolygonOf_scaleHeight_iff`: fields; `le_points` via `embedTop`-style `WithTop.map` monotonicity (`WithTop.map_le_iff`-free: the embedding of 3); `greatest`: a competitor `g` for `scaleHeight c v` gives `scaleHeight c⁻¹ g` for `v` (3 with `inv_pos.mpr hc`; `scaleHeight c⁻¹ (scaleHeight c x) = x` by `WithTop.map_map`-style cases and `inv_mul_cancel_left₀ hc.ne'`), and conversely.
5. `isAdmissible_scaleHeight_iff`: `isAdmissible_iff_exists_line` both sides: `y + σ k ≤ v k ↔ c y + c σ k ≤ scaleHeight c v k` (cases on `v k`; `WithTop.map_coe`, `WithTop.coe_le_coe`, `mul_le_mul_left hc`, `mul_add`); conversely scale by `c⁻¹`.
6. `newtonPolygon_scaleHeight`: spec of `v`, 4, `eq_newtonPolygon`.
7. `slopeMultiset_scaleHeight`: `slopeIndices (scaleHeight c h) = slopeIndices h` (`mem_slopeIndices_iff`, 1 at `k`, `k+1` — or 2 with `WithTop.map_eq_top_iff`); unfold `slopeMultiset` with `dif_pos` on both sides, `Multiset.map_map`, and `(WithTop.map (c * ·) x).untop₀ = c * x.untop₀` (cases).
Decomposition entry: L2.18–L2.25.
#### Mathlib lemmas needed
`WithTop.map_eq_top_iff`, `NewtonPolygon.mem_finiteSupport`, `NewtonPolygon.unitSlope_nat`, `WithTop.ne_top_iff_exists`, `WithTop.map_coe`, `WithTop.map_top`, `WithTop.LinearOrderedAddCommGroup.coe_sub`, `WithTop.LinearOrderedAddCommGroup.top_sub`, `WithTop.LinearOrderedAddCommGroup.sub_top`, `mul_sub`, `WithTop.strictMono_map_iff`, `strictMono_mul_left_of_pos`, `StrictMono.le_iff_le`, `inv_pos`, `inv_mul_cancel_left₀`, `NewtonPolygon.isAdmissible_iff_exists_line`, `WithTop.coe_le_coe`, `mul_le_mul_left`, `mul_add`, `NewtonPolygon.mem_slopeIndices_iff`, `Multiset.map_map`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`.
#### Sources
[RM] §2.2.8 (Q-RM-2.2.8: "differ by the positive scalar … in height").
#### Generality decision
Positive scalar `c` where the order matters (3–7); the bookkeeping lemmas 1–2 hold for every `c`.

### [T015] Every slope index lies in a segment; the slope of a segment
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T014 · **Parallel**: yes (with T001, T039) · **Type**: theorems
- **Leaves**: L2.26–L2.27

#### Statement
```lean
theorem exists_isSegment_of_mem_slopeIndices (hh : IsConvexSeq h) (hfin : (slopeIndices h).Finite)
    {j : ℕ} (hj : j ∈ slopeIndices h) : ∃ a b, IsSegment h a b ∧ a ≤ j ∧ j < b := by sorry

theorem IsConvexSeq.unitSlope_eq_div_of_isSegment (hh : IsConvexSeq h) {a b : ℕ}
    (hab : IsSegment h a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    unitSlope h j = ((((h b).untop₀ - (h a).untop₀) / ((b : ℝ) - a) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `exists_isSegment_of_mem_slopeIndices`: `hj` gives `h j ≠ ⊤`, `h (j+1) ≠ ⊤` (`mem_slopeIndices_iff`). Let `S := slopeIndices h` (finite, nonempty), `j₁ := hfin.toFinset.max'`-style largest element (`Set.Finite.bddAbove`, `Nat.sSup_mem`), `d := j₁ + 1`: then `h d ≠ ⊤` and `h (d + 1) = ⊤` (else `d ∈ S`), so `IsVertex h d` (`isVertex_of_succ_eq_top hh`). The anchor is a vertex (`isVertex_anchor ⟨j, hj.1⟩`) with `anchor h ≤ j` (`anchor_le hj.1`). Set `a := sSup {i | i ≤ j ∧ IsVertex h i}` (bounded by `j`, nonempty; `Nat.sSup_mem`) and `b := sInf {i | j < i ∧ IsVertex h i}` (nonempty: `d`, since `j < d`; `Nat.sInf_mem`). Then `IsSegment h a b`: both vertices, `a ≤ j < b`, and no vertex strictly between: a vertex `i` with `a < i < b` would be either `≤ j` (then `i ≤ a` by `le_csSup`/`Nat.le_sSup`-style, contradiction) or `> j` (then `b ≤ i`, contradiction).
2. `IsConvexSeq.unitSlope_eq_div_of_isSegment`: `IsConvexSeq.unitSlope_eq_of_isSegment hh hab haj hjb` gives `unitSlope h j = unitSlope h a`; `IsConvexSeq.eq_add_nsmul_of_isSegment hh hab le_rfl hab.2.2.1.le` at `k = b`: `h b = h a + (b - a) • unitSlope h a`; with `h a = ↑α`, `h b = ↑β` (vertices are finite, `WithTop.ne_top_iff_exists`), `unitSlope h a` is finite (`unitSlope_ne_top`), write it as `↑s`; `WithTop.coe_nsmul`, `WithTop.coe_add`, `WithTop.coe_inj`, `nsmul_eq_mul`: `β = α + (b - a) * s`, so `s = (β - α) / ((b:ℝ) - a)` (`eq_div_iff`, `Nat.cast_sub hab.2.2.1.le`, `sub_ne_zero.mpr`), and `untop₀` of the coercions by `WithTop.untop₀_coe`.
Decomposition entry: L2.26–L2.27.
#### Mathlib lemmas needed
`NewtonPolygon.mem_slopeIndices_iff`, `Set.Finite.bddAbove`, `Nat.sSup_mem`, `Nat.sInf_mem`, `Nat.sInf_le`, `le_csSup`, `NewtonPolygon.isVertex_of_succ_eq_top`, `NewtonPolygon.isVertex_anchor`, `NewtonPolygon.anchor_le`, `NewtonPolygon.IsSegment`, `NewtonPolygon.IsConvexSeq.unitSlope_eq_of_isSegment`, `NewtonPolygon.IsConvexSeq.eq_add_nsmul_of_isSegment`, `NewtonPolygon.unitSlope_ne_top`, `WithTop.ne_top_iff_exists`, `WithTop.coe_nsmul`, `WithTop.coe_add`, `WithTop.coe_inj`, `WithTop.untop₀_coe`, `nsmul_eq_mul`, `eq_div_iff`, `Nat.cast_sub`, `sub_ne_zero`.
#### Sources
[Kob84] IV §3 p. 97 (Q-Kob-vert: "its slope is (m' − m)/(i' − i)"); [Gou20] p. 252 (Q-Gou-feat).
#### Generality decision
Generic over convex `h` with finitely many slopes (polygons of polynomials); a terminal ray has no right vertex, hence the finiteness hypothesis (plan D4).

### [CLEANUP-5] Run /cleanup on `Generic.lean`
- **Status**: open · **File**: `Generic.lean` · **Depends on**: T015 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T016] `PowerSeries.coeffVal`: the points, `⊤` at vanishing coefficients, the term dictionary
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: CLEANUP-3 · **Parallel**: yes (with T063) · **Type**: def API
- **Leaves**: L3.1–L3.10

#### Statement
```lean
noncomputable def coeffVal : ℕ → WithTop ℝ := fun i ↦ v.embedTop (v (coeff i f))

@[simp] lemma coeffVal_eq_top_iff {i : ℕ} : coeffVal v f i = ⊤ ↔ coeff i f = 0 := by sorry

lemma coeffVal_ne_top_iff {i : ℕ} : coeffVal v f i ≠ ⊤ ↔ coeff i f ≠ 0 := by sorry

lemma coeffVal_eq_coe_iff {i : ℕ} {γ : Γ} :
    coeffVal v f i = (v.embed γ : WithTop ℝ) ↔ v (coeff i f) = (γ : WithTop Γ) := by sorry

lemma finiteSupport_coeffVal : finiteSupport (coeffVal v f) = {i | coeff i f ≠ 0} := by sorry

@[simp] lemma coeffVal_zero : coeffVal v (0 : PowerSeries K) = fun _ ↦ ⊤ := by sorry

lemma coeffVal_zero_of_coeff_zero_eq_one (h : coeff 0 f = 1) : coeffVal v f 0 = 0 := by sorry

lemma exists_coeffVal_ne_top (hf : f ≠ 0) : ∃ i, coeffVal v f i ≠ ⊤ := by sorry

lemma norm_coeff_mul_rpow_pow_le_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k ≤ 1 ↔ ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

lemma norm_coeff_mul_rpow_pow_lt_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k < 1 ↔ ((m * k : ℝ) : WithTop ℝ) < coeffVal v f k := by sorry

lemma norm_coeff_mul_rpow_pow_eq_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k = 1 ↔ coeffVal v f k = ((m * k : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
`coeffVal v f i = v.embedTop (v (coeff i f))` (no `sorry`).
1. `coeffVal_eq_top_iff := v.embedTop_apply_eq_top_iff`; `_ne_top_iff := coeffVal_eq_top_iff.not`.
2. `coeffVal_eq_coe_iff`: (←) `rw [h, embedTop_coe]`; (→) `v (coeff i f) ≠ ⊤` (else the left side is `⊤`), obtain `γ'` (`WithTop.ne_top_iff_exists`), `embedTop_coe`, `WithTop.coe_inj`, `v.strictMono_embed.injective`.
3. `finiteSupport_coeffVal`: `Set.ext`, `mem_finiteSupport`, 1. `coeffVal_zero`: `funext`, `map_zero`, `v.map_zero`, `embedTop_top`. `coeffVal_zero_of_coeff_zero_eq_one`: `rw [coeffVal_apply, h, v.embedTop_map_one]`.
4. `exists_coeffVal_ne_top`: `PowerSeries.ext_iff` negated gives `i` with `coeff i f ≠ 0`; 1.
5. `norm_coeff_mul_rpow_pow_{le,lt,eq}_one_iff := v.norm_mul_rpow_pow_{le,lt,eq}_one_iff (coeff k f) m k`.
Decomposition entry: L3.1–L3.10.
#### Mathlib lemmas needed
`WithTop.ne_top_iff_exists`, `WithTop.coe_inj`, `StrictMono.injective`, `NewtonPolygon.mem_finiteSupport`, `map_zero`, `PowerSeries.ext_iff`, `funext`.
#### Sources
[RM] §2.1.1; [Kob84] IV §3 (Q-Kob-def: "If a_i = 0, we omit that point, or we think of it as lying \"infinitely\" far above"); [Gou20] (Q-Gou-def).
#### Generality decision
`[NormedField K]`, any `Γ`; `f` any power series.

### [T017] Bounded terms are a line below the points; admissible iff bounded somewhere
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: T016 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L3.11–L3.12

#### Statement
```lean
theorem hasGaussNorm_rpow_iff_exists_line (m : ℝ) :
    HasGaussNorm norm (v.base ^ m) f ↔
      ∃ y : ℝ, ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

theorem isAdmissible_coeffVal_iff_exists_hasGaussNorm :
    IsAdmissible (coeffVal v f) ↔ ∃ c : ℝ, 0 < c ∧ HasGaussNorm norm c f := by sorry
```
#### Proof sketch
1. `hasGaussNorm_rpow_iff_exists_line`: `HasGaussNorm norm c f` unfolds to `BddAbove (Set.range fun k ↦ ‖coeff k f‖ * c ^ k)` (`bddAbove_def`, `Set.forall_mem_range`).
   (→) obtain `M`. If `M ≤ 0`: every term is `0` (`le_antisymm` with `mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_pos_of_pos v.base_pos m).le _)`), so every coefficient vanishes (`mul_eq_zero`, `pow_ne_zero`, `norm_eq_zero`), `coeffVal = ⊤` (T016) and any `y` works (`le_top`). If `0 < M`: `y := -Real.logb v.base M`; for each `k`, if `coeff k f = 0` then `_ ≤ ⊤`; else `v (coeff k f) = ↑γ`, `norm_mul_rpow_pow_eq_rpow`, `M = b ^ (-y)` (`v.rpow_logb`, `neg_neg`), `Real.rpow_le_rpow_left_iff v.one_lt_base`: `mk - eγ ≤ -y ↔ y + mk ≤ eγ`; `embedTop_coe`, `WithTop.coe_le_coe`.
   (←) given `y`, bound `M := b ^ (-y)`: each term is `0 ≤ M` or `b ^ (mk - eγ) ≤ b ^ (-y)` by the same rewriting.
2. `isAdmissible_coeffVal_iff_exists_hasGaussNorm`: `isAdmissible_iff_exists_line`; (→) a line of slope `σ` gives `HasGaussNorm` at `c := b ^ σ > 0` (`Real.rpow_pos_of_pos`) by 1; (←) `c > 0` is `b ^ (logb b c)` (`v.rpow_logb hc`), so 1 gives a line.
Decomposition entry: L3.11–L3.12.
#### Mathlib lemmas needed
`bddAbove_def`, `Set.forall_mem_range`, `mul_nonneg`, `norm_nonneg`, `pow_nonneg`, `Real.rpow_pos_of_pos`, `mul_eq_zero`, `pow_ne_zero`, `norm_eq_zero`, `Real.rpow_le_rpow_left_iff`, `WithTop.coe_le_coe`, `le_top`, `NewtonPolygon.isAdmissible_iff_exists_line`, `neg_neg`.
#### Sources
[RM] §2.1.3, §2.3.2 ("HasGaussNorm norm c f is equivalent to the supporting value being finite"); [Kob84] Lemma 5 proof (Q-Kob-L5: "ord_p(a_i x^i) = ord_p a_i − ib'").
#### Generality decision
Radius form through `v.base ^ m`; the positive-radius form is the second theorem.

### [T018] Bounded at a radius ⟹ restricted at every smaller radius
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: T017 · **Parallel**: yes (with T063) · **Type**: theorem
- **Leaves**: L3.13

#### Statement
```lean
theorem isRestricted_of_hasGaussNorm {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c < c')
    (hf : HasGaussNorm norm c' f) : IsRestricted c f := by sorry
```
#### Proof sketch
`PowerSeries.isRestricted_iff'` ([RAG]) reduces to `Tendsto (fun k ↦ ‖coeff k f‖ * c ^ k) atTop (𝓝 0)`. Let `M` bound the terms at `c'` (`hf`, `bddAbove_def`), `c' > 0` from `hc.trans_lt hcc'`, `r := c / c'` with `0 ≤ r < 1` (`div_nonneg`, `div_lt_one`). For each `k`, `‖aₖ‖ cᵏ = (‖aₖ‖ c'ᵏ) rᵏ` (`div_pow`, `mul_div_assoc`, `mul_div_cancel₀`-style with `pow_ne_zero`) `≤ M rᵏ` (`mul_le_mul_of_nonneg_right`, `pow_nonneg`). Conclude with `squeeze_zero (fun k ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc k)) (bound) ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul M)` and `mul_zero`.
Decomposition entry: L3.13.
#### Mathlib lemmas needed
`PowerSeries.isRestricted_iff'`, `bddAbove_def`, `div_nonneg`, `div_lt_one`, `div_pow`, `mul_div_assoc`, `mul_div_cancel₀`, `pow_ne_zero`, `mul_le_mul_of_nonneg_right`, `pow_nonneg`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`, `mul_zero`, `norm_nonneg`.
#### Sources
[RM] §2.3.2 ("restrictedness is decay and is strictly stronger than boundedness. Prove the implication that holds"); [Kob84] Lemma 5 (Q-Kob-L5).
#### Generality decision
Any `[NormedRing]` would do; stated for the layer's `K`. `0 ≤ c < c'` are the honest hypotheses.

### [CLEANUP-6] Run /cleanup on `CoeffVal.lean`
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: T018 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [CLEANUP-ALL-1] Run /cleanup-all before milestone M1 (T019)
- **Status**: open · **Depends on**: CLEANUP-6, CLEANUP-3, CLEANUP-5 · **Parallel**: no · **Type**: cleanup
- Sweep before the milestone: `NormedAddValuation.lean`, `Generic.lean`, `CoeffVal.lean` so far. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T019] [M1] Admissibility is restrictedness at some positive radius; the vertical case
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorems · **Milestone**: M1 ([RM] §2.1.3)
- **Leaves**: L3.14–L3.16

#### Statement
```lean
theorem isAdmissible_coeffVal_iff_exists_isRestricted :
    IsAdmissible (coeffVal v f) ↔ ∃ c : ℝ, 0 < c ∧ IsRestricted c f := by sorry

theorem IsRestricted.isAdmissible_coeffVal {c : ℝ} (hc : 0 < c) (hf : IsRestricted c f) :
    IsAdmissible (coeffVal v f) := by sorry

theorem isVertical_coeffVal_iff :
    IsVertical (coeffVal v f) ↔ f ≠ 0 ∧ ∀ c : ℝ, 0 < c → ¬ IsRestricted c f := by sorry
```
#### Proof sketch
1. `isAdmissible_coeffVal_iff_exists_isRestricted`: `isAdmissible_coeffVal_iff_exists_hasGaussNorm` (T017); (→) from `c > 0` with `HasGaussNorm`, `isRestricted_of_hasGaussNorm (half_pos hc).le (half_lt_self hc)` at `c / 2 > 0`; (←) from `IsRestricted c f`, [RAG] `PowerSeries.IsRestricted.hasGaussNorm`.
2. `IsRestricted.isAdmissible_coeffVal := (isAdmissible_coeffVal_iff_exists_isRestricted v).mpr ⟨c, hc, hf⟩`.
3. `isVertical_coeffVal_iff`: unfold `NewtonPolygon.IsVertical`; the first conjunct is `f ≠ 0` by `exists_coeffVal_ne_top` and `coeffVal_ne_top_iff` + `PowerSeries.ext_iff`; the second is the negation of 1 (`not_exists`, `not_and`).
Decomposition entry: L3.14–L3.16.
#### Mathlib lemmas needed
`PowerSeries.IsRestricted.hasGaussNorm`, `half_pos`, `half_lt_self`, `NewtonPolygon.IsVertical`, `not_exists`, `not_and`, `PowerSeries.ext_iff`.
#### Sources
[RM] §2.1.3 ("admissible exactly when f is restricted at some positive radius"); [Kob84] IV §4 p. 99 (Q-Kob-degen: "zero radius of convergence").
#### Generality decision
Statement over the normed field; the radius is any positive real.

### [T020] `Polynomial.coeffVal`: finitely supported, admissible, the coercion
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: T019 · **Parallel**: yes (with T063) · **Type**: def API
- **Leaves**: L3.17–L3.24

#### Statement
```lean
noncomputable def coeffVal : ℕ → WithTop ℝ := fun i ↦ v.embedTop (v (coeff i f))

@[simp] lemma coeffVal_eq_top_iff {i : ℕ} : coeffVal v f i = ⊤ ↔ f.coeff i = 0 := by sorry

lemma coeffVal_ne_top_iff {i : ℕ} : coeffVal v f i ≠ ⊤ ↔ f.coeff i ≠ 0 := by sorry

lemma coeffVal_eq_coe_iff {i : ℕ} {γ : Γ} :
    coeffVal v f i = (v.embed γ : WithTop ℝ) ↔ v (f.coeff i) = (γ : WithTop Γ) := by sorry

lemma finiteSupport_coeffVal : finiteSupport (coeffVal v f) = ↑f.support := by sorry

lemma finiteSupport_coeffVal_finite : (finiteSupport (coeffVal v f)).Finite := by sorry

lemma coeffVal_coe : PowerSeries.coeffVal v (f : PowerSeries K) = coeffVal v f := by sorry

theorem isAdmissible_coeffVal : IsAdmissible (coeffVal v f) := by sorry

theorem hasGaussNorm_coe (c : ℝ) : PowerSeries.HasGaussNorm norm c (f : PowerSeries K) := by sorry
```
#### Proof sketch
The generator prints both `coeffVal` definitions; this ticket concerns the `Polynomial` one (second block).
1. `coeffVal_eq_top_iff`, `_ne_top_iff`, `_eq_coe_iff`: as T016 with `f.coeff i`.
2. `finiteSupport_coeffVal`: `Set.ext`, `mem_finiteSupport`, 1, `Polynomial.mem_support_iff`, `Finset.mem_coe`. `finiteSupport_coeffVal_finite`: rewrite and `Finset.finite_toSet`.
3. `coeffVal_coe`: `funext i`, `PowerSeries.coeffVal_apply`, `Polynomial.coeff_coe`.
4. `isAdmissible_coeffVal := NewtonPolygon.isAdmissible_of_finite (finiteSupport_coeffVal_finite v)`.
5. `hasGaussNorm_coe := (Polynomial.isRestricted_toPowerSeries c f).hasGaussNorm` ([RAG]).
Decomposition entry: L3.17–L3.24.
#### Mathlib lemmas needed
`NewtonPolygon.mem_finiteSupport`, `Polynomial.mem_support_iff`, `Finset.mem_coe`, `Finset.finite_toSet`, `Polynomial.coeff_coe`, `Polynomial.isRestricted_toPowerSeries`, `PowerSeries.IsRestricted.hasGaussNorm`.
#### Sources
[RM] §2.1.1 ("the sequence of a polynomial is finitely supported"), §2.1.3, §2.2.5.
#### Generality decision
As T016.

### [CLEANUP-7] Run /cleanup on `CoeffVal.lean`
- **Status**: open · **File**: `CoeffVal.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T021] `PowerSeries.newtonPolygon`: the specification, anchoring at `0`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: CLEANUP-5, CLEANUP-7 · **Parallel**: yes (with T039–T046, T063) · **Type**: def API
- **Leaves**: L4.1–L4.7

#### Statement
```lean
noncomputable def newtonPolygon : ℕ → WithTop ℝ := NewtonPolygon.newtonPolygon (coeffVal v f)

theorem isNewtonPolygonOf_newtonPolygon (hf : IsAdmissible (coeffVal v f)) :
    IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by sorry

theorem isNewtonPolygonOf_newtonPolygon_of_isRestricted {c : ℝ} (hc : 0 < c)
    (hf : IsRestricted c f) : IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by sorry

theorem newtonPolygon_le (hf : IsAdmissible (coeffVal v f)) (k : ℕ) :
    newtonPolygon v f k ≤ coeffVal v f k := by sorry

theorem isConvexSeq_newtonPolygon (hf : IsAdmissible (coeffVal v f)) :
    IsConvexSeq (newtonPolygon v f) := by sorry

@[simp] theorem newtonPolygon_zero : newtonPolygon v (0 : PowerSeries K) = fun _ ↦ ⊤ := by sorry

theorem newtonPolygon_zero_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) :
    newtonPolygon v f 0 = coeffVal v f 0 := by sorry

theorem newtonPolygon_zero_of_coeff_zero_eq_one (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f = 1) : newtonPolygon v f 0 = 0 := by sorry
```
#### Proof sketch
1. `isNewtonPolygonOf_newtonPolygon := NewtonPolygon.isNewtonPolygonOf_newtonPolygon (NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible.mpr hf)`; `_of_isRestricted` composes with `hf.isAdmissible_coeffVal hc` (T019).
2. `newtonPolygon_le := (isNewtonPolygonOf_newtonPolygon v hf).le_points k`; `isConvexSeq_newtonPolygon := (…).convex`.
3. `newtonPolygon_zero`: `rw [newtonPolygon_def, coeffVal_zero]`, `NewtonPolygon.newtonPolygon_eq_self NewtonPolygon.isConvexSeq_top`.
4. `newtonPolygon_zero_eq := (isNewtonPolygonOf_newtonPolygon v hf).anchor_eq (fun k hk ↦ absurd hk (Nat.not_lt_zero _)) ((coeffVal_ne_top_iff v).mpr h0)`.
5. `newtonPolygon_zero_of_coeff_zero_eq_one`: 4 with `h0 ▸ one_ne_zero`, then `coeffVal_zero_of_coeff_zero_eq_one`.
Decomposition entry: L4.1–L4.7.
#### Mathlib lemmas needed
`NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.le_points`, `NewtonPolygon.IsNewtonPolygonOf.convex`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `Nat.not_lt_zero`, `one_ne_zero`.
#### Sources
[RM] §2.2.1 ("prove the specification holds … under the hypotheses of §2.1.3"), §2.2.6; [Kob84] IV §4 (Q-Kob-ps); [Gou20] p. 260 (Q-Gou-ps).
#### Generality decision
Admissibility (or restrictedness at a positive radius) is the only hypothesis for the polygon to exist; the anchoring lemmas take `coeff 0 f ≠ 0`.

### [T022] Integrality at vertices and rationality on segments
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T021 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.8–L4.10

#### Statement
```lean
theorem exists_eq_embed_of_isVertex (hf : IsAdmissible (coeffVal v f)) {k : ℕ}
    (hk : IsVertex (newtonPolygon v f) k) :
    ∃ γ : Γ, v (coeff k f) = (γ : WithTop Γ) ∧ newtonPolygon v f k = (v.embed γ : WithTop ℝ) := by sorry

theorem exists_unitSlope_eq_div_of_isSegment (hf : IsAdmissible (coeffVal v f)) {a b : ℕ}
    (hab : IsSegment (newtonPolygon v f) a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    ∃ γ : Γ, unitSlope (newtonPolygon v f) j = ((v.embed γ / ((b : ℝ) - a) : ℝ) : WithTop ℝ) := by sorry

theorem exists_int_unitSlope_eq_div_of_isSegment {w : NormedAddValuation K ℤ}
    (he : ∀ n : ℤ, w.embed n = n) (hf : IsAdmissible (coeffVal w f)) {a b : ℕ}
    (hab : IsSegment (newtonPolygon w f) a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    ∃ n : ℤ, unitSlope (newtonPolygon w f) j = (((n : ℚ) / ((b - a : ℕ) : ℚ) : ℚ) : ℝ) := by sorry
```
#### Proof sketch
1. `exists_eq_embed_of_isVertex`: `(isNewtonPolygonOf_newtonPolygon v hf).eq_of_isVertex hk : h k = coeffVal v f k`; `hk.1 : h k ≠ ⊤` so `coeff k f ≠ 0` (`coeffVal_ne_top_iff`); `v.exists_eq_coe` gives `γ`; `⟨γ, hγ, by rw [heq, coeffVal_apply, hγ, embedTop_coe]⟩`.
2. `exists_unitSlope_eq_div_of_isSegment`: `IsConvexSeq.unitSlope_eq_div_of_isSegment (isConvexSeq_newtonPolygon v hf) hab haj hjb` (T015); from 1 at the vertices `a` and `b` (`hab.1`, `hab.2.1`) obtain `γ_a`, `γ_b` with `h a = ↑(e γ_a)`, `h b = ↑(e γ_b)`; `⟨γ_b - γ_a, _⟩` with `WithTop.untop₀_coe`, `map_sub`.
3. `exists_int_unitSlope_eq_div_of_isSegment`: 2 for `w`, then `he` rewrites `w.embed n = n`; `⟨n, _⟩` with `Rat.cast_div`, `Rat.cast_intCast`, `Rat.cast_natCast`, `Nat.cast_sub hab.2.2.1.le`.
Decomposition entry: L4.8–L4.10.
#### Mathlib lemmas needed
`NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.IsVertex`, `WithTop.untop₀_coe`, `map_sub`, `Rat.cast_div`, `Rat.cast_intCast`, `Rat.cast_natCast`, `Nat.cast_sub`.
#### Sources
[RM] §2.2.3 ("The height of the polygon at a vertex lies in the image of e. Every unit slope … is (e γ) / l … for Γ = ℤ every slope is a rational number whose denominator divides the length of its segment"); [Kob84] p. 97 (Q-Kob-vert); plan D4.
#### Generality decision
Rationality for unit slopes in a bounded segment (any series), not for a terminal ray (plan D4); the `ℤ` version takes the embedding to be the cast (`he`).

### [T023] Entire series: unbounded slopes tending to `+∞`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T022 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.11–L4.12

#### Statement
```lean
theorem slopesUnbounded_newtonPolygon_of_forall_isRestricted (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) :
    SlopesUnbounded (newtonPolygon v f) := by sorry

theorem tendsto_unitSlope_newtonPolygon (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) :
    Tendsto (unitSlope (newtonPolygon v f)) atTop (𝓝 ⊤) := by sorry
```
#### Proof sketch
1. `slopesUnbounded_newtonPolygon_of_forall_isRestricted`: `hadm := (hf 1 one_pos).isAdmissible_coeffVal one_pos`; apply `(isNewtonPolygonOf_newtonPolygon v hadm).slopesUnbounded_of_forall_line`: for `σ`, `(hf (v.base ^ σ) (Real.rpow_pos_of_pos v.base_pos σ)).hasGaussNorm` and `(hasGaussNorm_rpow_iff_exists_line v σ).mp` give the line.
2. `tendsto_unitSlope_newtonPolygon`: `WithTop.tendsto_nhds_top_iff`; fix `σ`; `Filter.eventually_atTop`. Let `h := newtonPolygon v f`, convex (T021). From 1's line at slope `σ + 1`: `y + (σ+1) k ≤ h k` for all `k` (`IsNewtonPolygonOf.line_le`). Claim: `∃ N, ∀ j ≥ N, ↑σ < unitSlope h j`. By contradiction (`not_exists`, `not_forall`, `not_lt`): for every `N` some `j ≥ N` has `unitSlope h j ≤ σ`; such `j` has `h j ≠ ⊤` and `h (j+1) ≠ ⊤` (`unitSlope_ne_top_iff`, since `≤ ↑σ < ⊤`), and by `IsConvexSeq.monotoneOn` every finite index `i ≤ j` has `unitSlope h i ≤ σ`; as `j` is unbounded, all finite indices do. Then for `k ≥ a := anchor h`, `h k ≤ h a + (k - a) • ↑σ` (`IsConvexSeq.le_add_nsmul_unitSlope_self` chained, or `eq_add_sum_unitSlope` with the termwise bound), while `h k ≥ ↑(y + (σ+1) k)`: for `k` large, `y + (σ+1)k > (h a).untop₀ + σ (k - a)` (`exists_nat_gt`), contradiction (`WithTop.coe_le_coe`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `linarith`).
Decomposition entry: L4.11–L4.12 (the first sketch's defect and its repair are recorded there).
#### Mathlib lemmas needed
`NewtonPolygon.IsNewtonPolygonOf.slopesUnbounded_of_forall_line`, `Real.rpow_pos_of_pos`, `PowerSeries.IsRestricted.hasGaussNorm`, `WithTop.tendsto_nhds_top_iff`, `Filter.eventually_atTop`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.unitSlope_ne_top_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.IsConvexSeq.le_add_nsmul_unitSlope_self`, `NewtonPolygon.eq_add_sum_unitSlope`, `NewtonPolygon.anchor_le`, `exists_nat_gt`, `WithTop.coe_le_coe`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `not_exists`, `not_forall`, `not_lt`.
#### Sources
[RM] §2.2.4 ("For a power series restricted at every positive radius (\"entire\"), prove SlopesUnbounded holds and the unit slopes tend to +∞"); [Gou20] Lemma 7.4.8 proof (Q-Gou-L748).
#### Generality decision
Entire = restricted at every positive radius; no anchoring hypothesis (unit slopes before the anchor are `⊤`, which is `> σ`).

### [CLEANUP-8] Run /cleanup on `PowerSeries.lean`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T023 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T024] A unit slope above `σ` forces restrictedness at `b ^ σ`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: CLEANUP-8 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.13–L4.14

#### Statement
```lean
theorem isRestricted_rpow_of_lt_unitSlope (hf : IsAdmissible (coeffVal v f)) {σ : ℝ} {j : ℕ}
    (hjf : newtonPolygon v f j ≠ ⊤) (hj : (σ : WithTop ℝ) < unitSlope (newtonPolygon v f) j) :
    IsRestricted (v.base ^ σ) f := by sorry

theorem unitSlope_le_of_not_isRestricted (hf : IsAdmissible (coeffVal v f)) {σ : ℝ}
    (hσ : ¬ IsRestricted (v.base ^ σ) f) {j : ℕ} (hjf : newtonPolygon v f j ≠ ⊤) :
    unitSlope (newtonPolygon v f) j ≤ σ := by sorry
```
#### Proof sketch
1. `isRestricted_rpow_of_lt_unitSlope` (`hjf : h j ≠ ⊤`, `hj : ↑σ < unitSlope h j`): `rcases eq_or_ne (unitSlope h j) ⊤`.
   - `⊤`: `unitSlope_eq_top_iff` with `hjf` gives `h (j+1) = ⊤`; `IsConvexSeq.eq_top_of_le` (anchor `≤ j`, `h j ≠ ⊤`) gives `h k = ⊤` for all `k ≥ j + 1`; `newtonPolygon_le` and `top_le_iff` give `coeffVal v f k = ⊤`, i.e. `coeff k f = 0` for `k > j`: `f` has finite support (`Set.Finite.subset (Set.finite_Iic j)`), so [RAG] `PowerSeries.isRestricted_of_finite_support`.
   - real `τ := (unitSlope h j).untop₀`, `σ < τ`: for `k ≥ j`, `h k ≥ h j + (k - j) • unitSlope h j` (`IsConvexSeq.add_nsmul_unitSlope_le`), so with `h j = ↑η`, `coeffVal v f k ≥ ↑(η + (k - j) τ)`. Term bound: for `k ≥ j` with `coeff k f ≠ 0`, `‖aₖ‖ (b^σ)^k = b ^ (σ k - e γₖ) ≤ b ^ (σ k - η - (k - j) τ) = C · (b ^ (σ - τ)) ^ k` (`norm_coeff_mul_rpow_pow_eq_rpow`-style via T004's `norm_mul_rpow_pow_eq_rpow`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`), `0 ≤ b ^ (σ - τ) < 1` (`Real.rpow_lt_one_of_one_lt_of_neg`, `sub_neg.mpr`); conclude by [RAG] `isRestricted_iff'`, `squeeze_zero'` with `Filter.eventually_atTop` (from `j`) and `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`.
2. `unitSlope_le_of_not_isRestricted := not_lt.mp fun hlt ↦ hσ (isRestricted_rpow_of_lt_unitSlope v hf hjf hlt)`.
Decomposition entry: L4.13–L4.14 (the statement repair `hjf` is recorded there).
#### Mathlib lemmas needed
`NewtonPolygon.unitSlope_eq_top_iff`, `NewtonPolygon.IsConvexSeq.eq_top_of_le`, `NewtonPolygon.anchor_le`, `top_le_iff`, `Set.Finite.subset`, `Set.finite_Iic`, `PowerSeries.isRestricted_of_finite_support`, `NewtonPolygon.IsConvexSeq.add_nsmul_unitSlope_le`, `WithTop.ne_top_iff_exists`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_lt_one_of_one_lt_of_neg`, `sub_neg`, `PowerSeries.isRestricted_iff'`, `squeeze_zero'`, `Filter.eventually_atTop`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`, `not_lt`.
#### Sources
[RM] §2.2.4 with the direction corrected (plan D2); [Kob84] Lemma 5 (Q-Kob-L5); [SRC] `RadiusOfConvergence.isRestricted_of_lt_slope`, `not_isRestricted_of_slopes_le`. [SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`.
#### Generality decision
The index must be finite for the polygon (`hjf`); the radius is `v.base ^ σ`.

### [T025] Multiplying by a constant translates the polygon
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T024 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.15–L4.18

#### Statement
```lean
theorem coeffVal_C_mul {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    coeffVal v (C c * f) = fun k ↦ coeffVal v f k + (v.embed γ : WithTop ℝ) := by sorry

theorem newtonPolygon_C_mul (hf : IsAdmissible (coeffVal v f)) {c : K} {γ : Γ}
    (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (C c * f) = fun k ↦ newtonPolygon v f k + (v.embed γ : WithTop ℝ) := by sorry

theorem coeff_zero_C_inv_mul (h0 : coeff 0 f ≠ 0) : coeff 0 (C ((coeff 0 f)⁻¹) * f) = 1 := by sorry

theorem newtonPolygon_C_inv_mul (hf : IsAdmissible (coeffVal v f)) {γ : Γ}
    (h0 : v (coeff 0 f) = (γ : WithTop Γ)) :
    newtonPolygon v (C ((coeff 0 f)⁻¹) * f) =
      fun k ↦ newtonPolygon v f k + ((-v.embed γ : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `coeffVal_C_mul`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_C_mul`, `v.map_mul`, `hc`, `embedTop_add`, `embedTop_coe`, `add_comm`.
2. `newtonPolygon_C_mul`: `rw [newtonPolygon_def, coeffVal_C_mul v hc]`, then `NewtonPolygon.newtonPolygon_add_const hf (v.embed γ)`.
3. `coeff_zero_C_inv_mul`: `PowerSeries.coeff_C_mul`, `inv_mul_cancel₀ h0`.
4. `newtonPolygon_C_inv_mul`: 2 with `c := (coeff 0 f)⁻¹` and `v c = ↑(-γ)` (`v.map_inv`, `h0`, `LinearOrderedAddCommGroup.coe_neg`), then `map_neg` of `e`.
Decomposition entry: L4.15–L4.18.
#### Mathlib lemmas needed
`PowerSeries.coeff_C_mul`, `NewtonPolygon.newtonPolygon_add_const`, `inv_mul_cancel₀`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `map_neg`, `add_comm`.
#### Sources
[RM] §2.2.6 ("every series with coeff 0 f ≠ 0 becomes so after dividing by coeff 0 f, with the polygon translated by a constant"); [Gou20] Problem 340 (Q-Gou-P340).
#### Generality decision
Any nonzero constant (encoded as `v c = ↑γ`).

### [T026] `f (cX)` shears the polygon; `X ^ n * f` shifts it
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T025 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.19–L4.22

#### Statement
```lean
theorem coeffVal_rescale {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    coeffVal v (rescale c f) = fun k ↦ coeffVal v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by sorry

theorem newtonPolygon_rescale (hf : IsAdmissible (coeffVal v f)) {c : K} {γ : Γ}
    (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (rescale c f) =
      fun k ↦ newtonPolygon v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by sorry

theorem coeffVal_X_pow_mul (n : ℕ) : coeffVal v (X ^ n * f) = shiftRight n (coeffVal v f) := by sorry

theorem newtonPolygon_X_pow_mul (hf : IsAdmissible (coeffVal v f)) (n : ℕ) :
    newtonPolygon v (X ^ n * f) = shiftRight n (newtonPolygon v f) := by sorry
```
#### Proof sketch
1. `coeffVal_rescale`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_rescale` (`c ^ k * coeff k f`), `v.map_mul`, `v.map_pow`, `hc`, `WithTop.coe_nsmul`, `embedTop_add`, `embedTop_coe`, `map_nsmul`, `nsmul_eq_mul`, `add_comm`.
2. `newtonPolygon_rescale`: `rw [newtonPolygon_def, coeffVal_rescale v hc]`; `NewtonPolygon.newtonPolygon_add_affine hf 0 (v.embed γ)` and `zero_add` inside the coercion (`funext`, `congr`).
3. `coeffVal_X_pow_mul`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_X_pow_mul'`, `NewtonPolygon.shiftRight`; `split_ifs`: `coeffVal_apply` or `map_zero`, `v.map_zero`, `embedTop_top`.
4. `newtonPolygon_X_pow_mul`: `rw [newtonPolygon_def, coeffVal_X_pow_mul]`, `NewtonPolygon.newtonPolygon_shiftRight hf n` (T011).
Decomposition entry: L4.19–L4.22.
#### Mathlib lemmas needed
`PowerSeries.coeff_rescale`, `WithTop.coe_nsmul`, `map_nsmul`, `nsmul_eq_mul`, `NewtonPolygon.newtonPolygon_add_affine`, `zero_add`, `PowerSeries.coeff_X_pow_mul'`, `map_zero`.
#### Sources
[RM] §2.2.7 ("the polygon of f (cX) is sheared by e (v c), the polygon of X^n · f is translated right by n"); [Kob84] p. 101 (Q-Kob-shear).
#### Generality decision
`rescale c f = f (cX)` for any `c ≠ 0` (as `v c = ↑γ`); `n` any natural.

### [CLEANUP-9] Run /cleanup on `PowerSeries.lean`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T026 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T027] Compatible base change and change of valuation
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: CLEANUP-9 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L4.23–L4.27

#### Statement
```lean
theorem coeffVal_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : coeffVal w (map φ f) = coeffVal v f := by sorry

theorem newtonPolygon_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : newtonPolygon w (map φ f) = newtonPolygon v f := by sorry

theorem coeffVal_eq_scaleHeight : coeffVal w f = scaleHeight (v.scale w) (coeffVal v f) := by sorry

theorem isAdmissible_coeffVal_iff : IsAdmissible (coeffVal w f) ↔ IsAdmissible (coeffVal v f) := by sorry

theorem newtonPolygon_eq_scaleHeight (hf : IsAdmissible (coeffVal v f)) :
    newtonPolygon w f = scaleHeight (v.scale w) (newtonPolygon v f) := by sorry
```
#### Proof sketch
1. `coeffVal_map`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_map`, `hφ`, `NormedAddValuation.embedTop_apply`, `he`.
2. `newtonPolygon_map`: `simp only [newtonPolygon_def, coeffVal_map v w φ hφ he]`.
3. `coeffVal_eq_scaleHeight`: `funext k`; `coeffVal_apply`, `NewtonPolygon.scaleHeight_apply`, `v.embedTop_apply_eq_map w` (T006).
4. `isAdmissible_coeffVal_iff`: `rw [coeffVal_eq_scaleHeight v w]`, `NewtonPolygon.isAdmissible_scaleHeight_iff (v.scale_pos w)`.
5. `newtonPolygon_eq_scaleHeight`: `rw [newtonPolygon_def, coeffVal_eq_scaleHeight v w]`, `NewtonPolygon.newtonPolygon_scaleHeight (v.scale_pos w) hf`.
Decomposition entry: L4.23–L4.27.
#### Mathlib lemmas needed
`PowerSeries.coeff_map`, `NewtonPolygon.isAdmissible_scaleHeight_iff`, `NewtonPolygon.newtonPolygon_scaleHeight`, `funext`.
#### Sources
[RM] §2.2.7 ("unchanged under an isometric scalar extension L/K carrying a compatible normed additive valuation"), §2.2.8 (Q-RM-2.2.8); plan D7, D9.
#### Generality decision
The extension is any ring hom `φ` with compatible `w` (plan D7); the change of valuation any second bundle on `K`.

### [CLEANUP-10] Run /cleanup on `PowerSeries.lean`
- **Status**: open · **File**: `PowerSeries.lean` · **Depends on**: T027 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T028] `Polynomial.newtonPolygon`: coercion, specification
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: CLEANUP-10 · **Parallel**: yes (with T039–T046, T063) · **Type**: def API
- **Leaves**: L5.1–L5.5

#### Statement
```lean
noncomputable def newtonPolygon : ℕ → WithTop ℝ := NewtonPolygon.newtonPolygon (coeffVal v f)

theorem newtonPolygon_coe : PowerSeries.newtonPolygon v (f : PowerSeries K) = newtonPolygon v f := by sorry

theorem isNewtonPolygonOf_newtonPolygon : IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by sorry

theorem newtonPolygon_le (k : ℕ) : newtonPolygon v f k ≤ coeffVal v f k := by sorry

theorem isConvexSeq_newtonPolygon : IsConvexSeq (newtonPolygon v f) := by sorry

@[simp] theorem newtonPolygon_zero : newtonPolygon v (0 : Polynomial K) = fun _ ↦ ⊤ := by sorry
```
#### Proof sketch
1. `newtonPolygon_coe`: `rw [PowerSeries.newtonPolygon_def, newtonPolygon_def, coeffVal_coe]`.
2. `isNewtonPolygonOf_newtonPolygon := NewtonPolygon.isNewtonPolygonOf_newtonPolygon (NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible.mpr (isAdmissible_coeffVal v))`; `newtonPolygon_le`, `isConvexSeq_newtonPolygon` are its fields.
3. `newtonPolygon_zero`: `coeffVal v 0 = fun _ ↦ ⊤` (`funext`, `Polynomial.coeff_zero`, `v.map_zero`, `embedTop_top`), then `newtonPolygon_eq_self isConvexSeq_top`.
Decomposition entry: L5.1–L5.5.
#### Mathlib lemmas needed
`NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `Polynomial.coeff_zero`.
#### Sources
[RM] §2.2.1, §2.2.5 ("the polygon of a polynomial, viewed as a power series, is the polygon of the polynomial").
#### Generality decision
No hypothesis: every polynomial has a polygon.

### [T029] The polygon is `⊤` exactly outside `[natTrailingDegree f, natDegree f]`
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T028 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.6–L5.9

#### Statement
```lean
theorem newtonPolygon_eq_top_of_lt_natTrailingDegree {k : ℕ} (hk : k < f.natTrailingDegree) :
    newtonPolygon v f k = ⊤ := by sorry

theorem newtonPolygon_eq_top_of_natDegree_lt {k : ℕ} (hk : f.natDegree < k) :
    newtonPolygon v f k = ⊤ := by sorry

theorem newtonPolygon_ne_top (hf : f ≠ 0) {k : ℕ} (h₁ : f.natTrailingDegree ≤ k)
    (h₂ : k ≤ f.natDegree) : newtonPolygon v f k ≠ ⊤ := by sorry

theorem newtonPolygon_eq_top_iff (hf : f ≠ 0) {k : ℕ} :
    newtonPolygon v f k = ⊤ ↔ k < f.natTrailingDegree ∨ f.natDegree < k := by sorry
```
#### Proof sketch
1. `_of_lt_natTrailingDegree`: `(isNewtonPolygonOf_newtonPolygon v).eq_top_of_forall_eq_top`: for `j ≤ k < natTrailingDegree f`, `coeff f j = 0` (`Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`), `coeffVal_eq_top_iff`.
2. `_of_natDegree_lt`: `.eq_top_of_forall_le` with `Polynomial.coeff_eq_zero_of_natDegree_lt` for `j ≥ k > natDegree f`.
3. `newtonPolygon_ne_top`: `.ne_top_of_le_of_le` with `a := natTrailingDegree f` (`coeffVal_ne_top_iff`: the trailing coefficient `f.coeff f.natTrailingDegree = f.trailingCoeff ≠ 0`, `Polynomial.trailingCoeff_eq_zero.not.mpr hf`) and `b := natDegree f` (`Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_eq_zero.not.mpr hf`).
4. `newtonPolygon_eq_top_iff`: `⟨fun h ↦ by_contra (fun hn ↦ newtonPolygon_ne_top v hf (not_lt.mp (not_or.mp hn).1) (not_lt.mp (not_or.mp hn).2) h), fun h ↦ h.elim (newtonPolygon_eq_top_of_lt_natTrailingDegree v) (newtonPolygon_eq_top_of_natDegree_lt v)⟩`.
Decomposition entry: L5.6–L5.9.
#### Mathlib lemmas needed
`NewtonPolygon.IsNewtonPolygonOf.eq_top_of_forall_eq_top`, `NewtonPolygon.IsNewtonPolygonOf.eq_top_of_forall_le`, `NewtonPolygon.IsNewtonPolygonOf.ne_top_of_le_of_le`, `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.trailingCoeff_eq_zero`, `Polynomial.trailingCoeff`, `Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_eq_zero`, `not_or`, `not_lt`.
#### Sources
[RM] §2.2.2 ("anchored at the order of vanishing at 0, its last vertex is at the degree"), §0.2.5.
#### Generality decision
`f ≠ 0` only where a finite value is asserted.

### [T030] Anchor, last point and the two end vertices
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T029 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.10–L5.14

#### Statement
```lean
theorem newtonPolygon_natTrailingDegree (hf : f ≠ 0) :
    newtonPolygon v f f.natTrailingDegree = coeffVal v f f.natTrailingDegree := by sorry

theorem newtonPolygon_natDegree (hf : f ≠ 0) :
    newtonPolygon v f f.natDegree = coeffVal v f f.natDegree := by sorry

theorem anchor_newtonPolygon (hf : f ≠ 0) : anchor (newtonPolygon v f) = f.natTrailingDegree := by sorry

theorem isVertex_natTrailingDegree (hf : f ≠ 0) :
    IsVertex (newtonPolygon v f) f.natTrailingDegree := by sorry

theorem isVertex_natDegree (hf : f ≠ 0) : IsVertex (newtonPolygon v f) f.natDegree := by sorry
```
#### Proof sketch
1. `newtonPolygon_natTrailingDegree := (isNewtonPolygonOf_newtonPolygon v).anchor_eq (fun k hk ↦ (coeffVal_eq_top_iff v).mpr (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk)) ((coeffVal_ne_top_iff v).mpr (Polynomial.trailingCoeff_eq_zero.not.mpr hf))`.
2. `isVertex_natDegree := NewtonPolygon.isVertex_of_succ_eq_top (isConvexSeq_newtonPolygon v) (newtonPolygon_ne_top v hf (Polynomial.natTrailingDegree_le_natDegree f) le_rfl) (newtonPolygon_eq_top_of_natDegree_lt v (Nat.lt_succ_self _))`.
3. `newtonPolygon_natDegree := (isNewtonPolygonOf_newtonPolygon v).eq_of_isVertex (isVertex_natDegree v hf)`.
4. `anchor_newtonPolygon`: `le_antisymm (NewtonPolygon.anchor_le (newtonPolygon_ne_top v hf le_rfl (natTrailingDegree_le_natDegree f)))` and `not_lt.mp fun h ↦ NewtonPolygon.anchor_mem ⟨_, …⟩ (newtonPolygon_eq_top_of_lt_natTrailingDegree v h)` (the anchor carries a finite value, `anchor_mem`).
5. `isVertex_natTrailingDegree`: `anchor_newtonPolygon v hf ▸ NewtonPolygon.isVertex_anchor ⟨_, newtonPolygon_ne_top v hf le_rfl (natTrailingDegree_le_natDegree f)⟩`.
Decomposition entry: L5.10–L5.14.
#### Mathlib lemmas needed
`NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `NewtonPolygon.isVertex_of_succ_eq_top`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.anchor_le`, `NewtonPolygon.anchor_mem`, `NewtonPolygon.isVertex_anchor`, `Polynomial.natTrailingDegree_le_natDegree`, `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`, `Polynomial.trailingCoeff_eq_zero`, `Nat.lt_succ_self`, `le_antisymm`, `not_lt`.
#### Sources
[RM] §2.2.2; [Gou20] p. 252 (Q-Gou-feat: "(0,0) and (n, v_p(a_n)) will always be vertices").
#### Generality decision
`f ≠ 0`.

### [CLEANUP-11] Run /cleanup on `Polynomial.lean`
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T030 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T031] The slope indices, unbounded slopes, anchoring at the origin
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: CLEANUP-11 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.15–L5.18

#### Statement
```lean
theorem slopeIndices_newtonPolygon (hf : f ≠ 0) :
    slopeIndices (newtonPolygon v f) = Set.Ico f.natTrailingDegree f.natDegree := by sorry

theorem slopeIndices_newtonPolygon_finite : (slopeIndices (newtonPolygon v f)).Finite := by sorry

theorem slopesUnbounded_newtonPolygon : SlopesUnbounded (newtonPolygon v f) := by sorry

theorem newtonPolygon_zero_of_coeff_zero_eq_one (h0 : f.coeff 0 = 1) : newtonPolygon v f 0 = 0 := by sorry
```
#### Proof sketch
1. `slopeIndices_newtonPolygon`: `Set.ext j`; `NewtonPolygon.mem_slopeIndices_iff`, `newtonPolygon_eq_top_iff v hf` at `j` and `j + 1` (negated: `not_or`, `not_lt`), `Set.mem_Ico`; `omega`.
2. `slopeIndices_newtonPolygon_finite := (isNewtonPolygonOf_newtonPolygon v).slopeIndices_finite (finiteSupport_coeffVal_finite v)`.
3. `slopesUnbounded_newtonPolygon := NewtonPolygon.slopesUnbounded_of_finite (slopeIndices_newtonPolygon_finite v)`.
4. `newtonPolygon_zero_of_coeff_zero_eq_one`: `(isNewtonPolygonOf_newtonPolygon v).anchor_eq (fun k hk ↦ absurd hk (Nat.not_lt_zero _)) _` then `coeffVal_apply`, `h0`, `v.embedTop_map_one`.
Decomposition entry: L5.15–L5.18.
#### Mathlib lemmas needed
`NewtonPolygon.mem_slopeIndices_iff`, `Set.mem_Ico`, `NewtonPolygon.IsNewtonPolygonOf.slopeIndices_finite`, `NewtonPolygon.slopesUnbounded_of_finite`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `Nat.not_lt_zero`, `not_or`, `not_lt`.
#### Sources
[RM] §2.2.2 ("exactly natDegree f - order f unit slopes, and SlopesUnbounded holds"), §2.2.6.
#### Generality decision
As T029.

### [T032] `newtonSlopes`: cardinality `natDegree − natTrailingDegree`, counts
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T031 · **Parallel**: yes (with T039–T046, T063) · **Type**: def API
- **Leaves**: L5.19–L5.20

#### Statement
```lean
variable (f) in
noncomputable def newtonSlopes : Multiset ℝ := slopeMultiset (newtonPolygon v f)

theorem card_newtonSlopes : (newtonSlopes v f).card = f.natDegree - f.natTrailingDegree := by sorry

theorem count_newtonSlopes (σ : ℝ) :
    (newtonSlopes v f).count σ = Set.ncard {j | unitSlope (newtonPolygon v f) j = σ} := by sorry
```
#### Proof sketch
`newtonSlopes v f = slopeMultiset (newtonPolygon v f)` (no `sorry`).
1. `card_newtonSlopes`: `NewtonPolygon.card_slopeMultiset (slopeIndices_newtonPolygon_finite v)` gives `(slopeIndices _).ncard`. `rcases eq_or_ne f 0`: for `f = 0`, `slopeIndices (newtonPolygon v 0) = ∅` (`newtonPolygon_zero`, `mem_slopeIndices_iff`, `unitSlope_eq_top_iff`), `Set.ncard_empty`, `Polynomial.natDegree_zero`, `Polynomial.natTrailingDegree_zero`; else `slopeIndices_newtonPolygon v hf`, `Set.ncard_eq_toFinset_card'`, `Set.toFinset_Ico`, `Nat.card_Ico`.
2. `count_newtonSlopes := NewtonPolygon.count_slopeMultiset (slopeIndices_newtonPolygon_finite v) σ`.
Decomposition entry: L5.19–L5.20.
#### Mathlib lemmas needed
`NewtonPolygon.card_slopeMultiset`, `NewtonPolygon.count_slopeMultiset`, `NewtonPolygon.mem_slopeIndices_iff`, `NewtonPolygon.unitSlope_eq_top_iff`, `Set.ncard_empty`, `Set.ncard_eq_toFinset_card'`, `Set.toFinset_Ico`, `Nat.card_Ico`, `Polynomial.natDegree_zero`, `Polynomial.natTrailingDegree_zero`.
#### Sources
[RM] §2.2.2 ("Define Polynomial.newtonSlopes v f : Multiset ℝ and prove its cardinality is natDegree f - order f"); [Gou20] (Q-Gou-feat); [Ked07] §1 (Q-Ked-def, cardinality).
#### Generality decision
Holds for `f = 0` too (both sides `0`).

### [T033] Rationality of the slopes of a polynomial
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T032 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.21–L5.23

#### Statement
```lean
theorem exists_isSegment_of_mem_slopeIndices {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon v f)) :
    ∃ a b, IsSegment (newtonPolygon v f) a b ∧ a ≤ j ∧ j < b := by sorry

theorem exists_unitSlope_eq_div {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon v f)) :
    ∃ (γ : Γ) (l : ℕ), 0 < l ∧
      unitSlope (newtonPolygon v f) j = ((v.embed γ / l : ℝ) : WithTop ℝ) := by sorry

theorem exists_int_unitSlope_eq_div {w : NormedAddValuation K ℤ} (he : ∀ n : ℤ, w.embed n = n)
    {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon w f)) :
    ∃ (a b : ℕ) (n : ℤ), IsSegment (newtonPolygon w f) a b ∧ a ≤ j ∧ j < b ∧
      unitSlope (newtonPolygon w f) j = (((n : ℚ) / ((b - a : ℕ) : ℚ) : ℚ) : ℝ) := by sorry
```
#### Proof sketch
1. `exists_isSegment_of_mem_slopeIndices := NewtonPolygon.exists_isSegment_of_mem_slopeIndices (isConvexSeq_newtonPolygon v) (slopeIndices_newtonPolygon_finite v) hj` (T015).
2. `exists_unitSlope_eq_div`: obtain `a, b, hab, haj, hjb` from 1; `rw [← newtonPolygon_coe] at *` and `PowerSeries.exists_unitSlope_eq_div_of_isSegment v (isAdmissible_coeffVal v |> (coeffVal_coe v).symm ▸ ·) hab haj hjb` (adjust the admissibility through `coeffVal_coe`), obtaining `γ`; `⟨γ, b - a, Nat.sub_pos_of_lt hjb_lt, by rwa [Nat.cast_sub hab.2.2.1.le]⟩`.
3. `exists_int_unitSlope_eq_div`: as 2 with `PowerSeries.exists_int_unitSlope_eq_div_of_isSegment he`, returning `⟨a, b, n, hab, haj, hjb, _⟩`.
Decomposition entry: L5.21–L5.23.
#### Mathlib lemmas needed
`Nat.sub_pos_of_lt`, `Nat.cast_sub`.
#### Sources
[RM] §2.2.3; [Kob84] p. 97 (Q-Kob-vert).
#### Generality decision
Every unit slope of a polynomial (all lie in bounded segments); the `ℤ` form takes `he`.

### [CLEANUP-12] Run /cleanup on `Polynomial.lean`
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T033 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [CLEANUP-ALL-2] Run /cleanup-all before milestone M2 (T034)
- **Status**: open · **Depends on**: CLEANUP-12, CLEANUP-10 · **Parallel**: no · **Type**: cleanup
- Sweep before the milestone: `PowerSeries.lean`, `Polynomial.lean` so far. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T034] [M2] The polygon of `reverse f` is the reflection
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: theorems · **Milestone**: M2 ([RM] §2.2.7)
- **Leaves**: L5.24–L5.25

#### Statement
```lean
theorem coeffVal_reverse : coeffVal v f.reverse = NewtonPolygon.reflect f.natDegree (coeffVal v f) := by sorry

theorem newtonPolygon_reverse :
    newtonPolygon v f.reverse = NewtonPolygon.reflect f.natDegree (newtonPolygon v f) := by sorry
```
#### Proof sketch
1. `coeffVal_reverse`: `funext k`; `coeffVal_apply`, `Polynomial.coeff_reverse`; `rcases le_or_lt k f.natDegree`: `Polynomial.revAt_le hk` and `NewtonPolygon.reflect_of_le hk`; else `Polynomial.revAt_eq_self_of_lt hk`, `Polynomial.coeff_eq_zero_of_natDegree_lt hk`, `v.map_zero`, `embedTop_top`, `NewtonPolygon.reflect_of_lt hk`.
2. `newtonPolygon_reverse`: `rw [newtonPolygon_def, newtonPolygon_def, coeffVal_reverse]`; `NewtonPolygon.newtonPolygon_reflect` (T013) with `hv : ∀ k, natDegree f < k → coeffVal v f k = ⊤` from `coeffVal_eq_top_iff` and `Polynomial.coeff_eq_zero_of_natDegree_lt`.
Decomposition entry: L5.24–L5.25.
#### Mathlib lemmas needed
`Polynomial.coeff_reverse`, `Polynomial.revAt_le`, `Polynomial.revAt_eq_self_of_lt`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `le_or_gt`.
#### Sources
[RM] §2.2.7 ("the polygon of Polynomial.reverse f is the reflection i ↦ h (d - i) … ⚠ … §6.2 depends on it; it is a milestone, not a remark").
#### Generality decision
Any polynomial (including `0`).

### [T035] `f (cX)` for polynomials: the coercion is `rescale`, the polygon is sheared
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T034 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.26–L5.27

#### Statement
```lean
theorem coe_comp_C_mul_X (c : K) :
    ((f.comp (C c * X) : Polynomial K) : PowerSeries K) = PowerSeries.rescale c (f : PowerSeries K) := by sorry

theorem newtonPolygon_comp_C_mul_X {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (f.comp (C c * X)) =
      fun k ↦ newtonPolygon v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `coe_comp_C_mul_X`: both sides are ring homs applied to `f`: `(Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.compRingHom (C c * X))` and `(PowerSeries.rescale c).comp Polynomial.coeToPowerSeries.ringHom`. Prove the equality of homs by `Polynomial.ringHom_ext`: on `C a`: `Polynomial.C_comp`, `Polynomial.coe_C`, and `PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a` (`PowerSeries.ext`, `coeff_rescale`, `PowerSeries.coeff_C`: `c ^ n * (if n = 0 then a else 0)`, `split_ifs`, `pow_zero`, `mul_zero`); on `X`: `Polynomial.X_comp`, `Polynomial.coe_mul`, `coe_C`, `coe_X`, `PowerSeries.rescale_X`. Then `DFunLike.congr_fun` at `f`.
2. `newtonPolygon_comp_C_mul_X`: `rw [← newtonPolygon_coe, coe_comp_C_mul_X, PowerSeries.newtonPolygon_rescale v _ hc, newtonPolygon_coe]` with admissibility from `isAdmissible_coeffVal v` transported by `coeffVal_coe`.
Decomposition entry: L5.26–L5.27 (plan D8).
#### Mathlib lemmas needed
`Polynomial.coeToPowerSeries.ringHom`, `Polynomial.compRingHom`, `Polynomial.ringHom_ext`, `Polynomial.C_comp`, `Polynomial.X_comp`, `Polynomial.coe_C`, `Polynomial.coe_X`, `Polynomial.coe_mul`, `PowerSeries.rescale_X`, `PowerSeries.coeff_rescale`, `PowerSeries.coeff_C`, `PowerSeries.ext`, `DFunLike.congr_fun`, `pow_zero`, `mul_zero`.
#### Sources
[RM] §2.2.7 ("the polygon of f (cX) is sheared by e (v c)"); [Kob84] p. 101 (Q-Kob-shear).
#### Generality decision
`c` any element (the shear statement names `γ` with `v c = ↑γ`, so `c ≠ 0`).

### [T036] Polynomial operations: shift, constants, base change, change of valuation
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T035 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L5.28–L5.33

#### Statement
```lean
theorem newtonPolygon_X_pow_mul (n : ℕ) :
    newtonPolygon v (X ^ n * f) = shiftRight n (newtonPolygon v f) := by sorry

theorem newtonPolygon_C_mul {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (C c * f) = fun k ↦ newtonPolygon v f k + (v.embed γ : WithTop ℝ) := by sorry

theorem newtonPolygon_C_inv_mul {γ : Γ} (h0 : v (f.coeff 0) = (γ : WithTop Γ)) :
    newtonPolygon v (C ((f.coeff 0)⁻¹) * f) =
      fun k ↦ newtonPolygon v f k + ((-v.embed γ : ℝ) : WithTop ℝ) := by sorry

theorem newtonPolygon_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : newtonPolygon w (f.map φ) = newtonPolygon v f := by sorry

theorem newtonPolygon_eq_scaleHeight :
    newtonPolygon w f = scaleHeight (v.scale w) (newtonPolygon v f) := by sorry

theorem newtonSlopes_eq_map : newtonSlopes w f = (newtonSlopes v f).map (fun t : ℝ ↦ v.scale w * t) := by sorry
```
#### Proof sketch
Each is the series statement (T025–T027) read through `newtonPolygon_coe` and the coercion lemmas, or the direct coefficient computation.
1. `newtonPolygon_X_pow_mul`: `rw [← newtonPolygon_coe, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.newtonPolygon_X_pow_mul v hadm n, newtonPolygon_coe]` (`hadm` from `isAdmissible_coeffVal v` via `coeffVal_coe`).
2. `newtonPolygon_C_mul`: same with `Polynomial.coe_C`, `PowerSeries.newtonPolygon_C_mul`. `newtonPolygon_C_inv_mul`: `PowerSeries.newtonPolygon_C_inv_mul` with `Polynomial.coeff_coe` for `coeff 0`.
3. `newtonPolygon_map`: `funext`-free: `simp only [newtonPolygon_def, coeffVal_apply, Polynomial.coeff_map, hφ, NormedAddValuation.embedTop_apply, he]`.
4. `newtonPolygon_eq_scaleHeight`: `coeffVal w f = scaleHeight (v.scale w) (coeffVal v f)` (`funext`, `v.embedTop_apply_eq_map w`), then `NewtonPolygon.newtonPolygon_scaleHeight (v.scale_pos w) (isAdmissible_coeffVal v)`.
5. `newtonSlopes_eq_map`: `newtonSlopes_def`, 4, `NewtonPolygon.slopeMultiset_scaleHeight (v.scale_pos w) (slopeIndices_newtonPolygon_finite v)`.
Decomposition entry: L5.28–L5.33.
#### Mathlib lemmas needed
`Polynomial.coe_mul`, `Polynomial.coe_pow`, `Polynomial.coe_X`, `Polynomial.coe_C`, `Polynomial.coeff_coe`, `Polynomial.coeff_map`, `NewtonPolygon.newtonPolygon_scaleHeight`, `NewtonPolygon.slopeMultiset_scaleHeight`.
#### Sources
[RM] §2.2.6–§2.2.8.
#### Generality decision
As the series versions.

### [CLEANUP-13] Run /cleanup on `Polynomial.lean`
- **Status**: open · **File**: `Polynomial.lean` · **Depends on**: T036 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T037] Compatibility of `ofNormAddVal` and `ofNormAddValQ` along an extension
- **Status**: open · **File**: `Extension.lean` · **Depends on**: CLEANUP-13 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L6.1–L6.4

#### Statement
```lean
theorem ofNormAddVal_algebraMap (x : K) : ofNormAddVal L (algebraMap K L x) = ofNormAddVal K x := by sorry

theorem ofNormAddVal_embed_eq : (ofNormAddVal L).embed = (ofNormAddVal K).embed := by sorry

theorem ofNormAddValQ_algebraMap (x : K) :
    ofNormAddValQ L (algebraMap K L π) (algebraMap K L x) = ofNormAddValQ K π x := by sorry

theorem ofNormAddValQ_embed_eq :
    (ofNormAddValQ L (algebraMap K L π)).embed = (ofNormAddValQ K π).embed := by sorry
```
#### Proof sketch
1. `ofNormAddVal_algebraMap`: `simpa using NormedField.normAddVal_algebraMap (L := L) x` (`ofNormAddVal_apply` is `rfl`).
2. `ofNormAddVal_embed_eq := rfl` (both `AddMonoidHom.id ℝ`).
3. `ofNormAddValQ_algebraMap`: `NormedField.normAddValQ_algebraMap π x` (Layer 1; the instance `NormedField.isCommensurable_algebraMap` supplies `(valuation (K := L)).IsCommensurable (algebraMap K L π)`).
4. `ofNormAddValQ_embed_eq := rfl`.
Decomposition entry: L6.1–L6.4.
#### Mathlib lemmas needed
`NormedField.normAddVal_algebraMap`, `NormedField.normAddValQ_algebraMap`, `NormedField.isCommensurable_algebraMap`.
#### Sources
[RM] §1.5.1–§1.5.2, §2.2.7 (plan D7).
#### Generality decision
`L` any ultrametric nontrivially normed `K`-algebra field for the real member; `K` complete and `L/K` algebraic for the rational member (Layer 1's hypotheses, explicit `variable`s).

### [T038] The polygon is unchanged under a compatible extension
- **Status**: open · **File**: `Extension.lean` · **Depends on**: T037 · **Parallel**: yes (with T039–T046, T063) · **Type**: theorems
- **Leaves**: L6.5–L6.8

#### Statement
```lean
theorem Polynomial.newtonPolygon_ofNormAddVal_map (f : Polynomial K) :
    Polynomial.newtonPolygon (ofNormAddVal L) (f.map (algebraMap K L)) =
      Polynomial.newtonPolygon (ofNormAddVal K) f := by sorry

theorem PowerSeries.newtonPolygon_ofNormAddVal_map (f : PowerSeries K) :
    PowerSeries.newtonPolygon (ofNormAddVal L) (PowerSeries.map (algebraMap K L) f) =
      PowerSeries.newtonPolygon (ofNormAddVal K) f := by sorry

theorem Polynomial.newtonPolygon_ofNormAddValQ_map (f : Polynomial K) :
    Polynomial.newtonPolygon (ofNormAddValQ L (algebraMap K L π)) (f.map (algebraMap K L)) =
      Polynomial.newtonPolygon (ofNormAddValQ K π) f := by sorry

theorem PowerSeries.newtonPolygon_ofNormAddValQ_map (f : PowerSeries K) :
    PowerSeries.newtonPolygon (ofNormAddValQ L (algebraMap K L π))
        (PowerSeries.map (algebraMap K L) f) =
      PowerSeries.newtonPolygon (ofNormAddValQ K π) f := by sorry
```
#### Proof sketch
Each is `Polynomial.newtonPolygon_map` / `PowerSeries.newtonPolygon_map` (T036 / T027) with `φ := algebraMap K L`, `hφ := ofNormAddVal_algebraMap` resp. `ofNormAddValQ_algebraMap π`, and `he := ofNormAddVal_embed_eq` resp. `ofNormAddValQ_embed_eq π`.
Decomposition entry: L6.5–L6.8.
#### Mathlib lemmas needed
`algebraMap`.
#### Sources
[RM] §2.2.7.
#### Generality decision
As T037. `ofNormAddValZ` is deliberately not covered (ramification scales the polygon; Layer 1 §1.3.6).

### [CLEANUP-14] Run /cleanup on `Extension.lean`
- **Status**: open · **File**: `Extension.lean` · **Depends on**: T038 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T039] `toEReal`: `WithTop ℝ` inside `EReal`
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: none · **Parallel**: yes (with T001, T010) · **Type**: def API
- **Leaves**: L7.1–L7.6

#### Statement
```lean
def toEReal (x : WithTop ℝ) : EReal := WithBot.some x

lemma toEReal_ne_bot (x : WithTop ℝ) : toEReal x ≠ ⊥ := by sorry

lemma toEReal_le_toEReal {x y : WithTop ℝ} : toEReal x ≤ toEReal y ↔ x ≤ y := by sorry

lemma toEReal_lt_toEReal {x y : WithTop ℝ} : toEReal x < toEReal y ↔ x < y := by sorry

lemma toEReal_injective : Function.Injective toEReal := by sorry

lemma toEReal_eq_top_iff {x : WithTop ℝ} : toEReal x = ⊤ ↔ x = ⊤ := by sorry

lemma toEReal_of_ne_top {x : WithTop ℝ} (hx : x ≠ ⊤) : toEReal x = ((x.untop₀ : ℝ) : EReal) := by sorry
```
#### Proof sketch
`toEReal x = WithBot.some x` and `EReal = WithBot (WithTop ℝ)` (a `def`; `toEReal_coe`, `toEReal_top` are `rfl`).
1. `toEReal_ne_bot := WithBot.coe_ne_bot`; `toEReal_le_toEReal := WithBot.coe_le_coe`; `toEReal_lt_toEReal := WithBot.coe_lt_coe`; `toEReal_injective := WithBot.coe_injective`. If the `EReal` instances do not unfold automatically, `show (WithBot.some x : WithBot (WithTop ℝ)) ≤ WithBot.some y ↔ _` first.
2. `toEReal_eq_top_iff`: `(⊤ : EReal) = toEReal ⊤` (`toEReal_top.symm`), then `toEReal_injective.eq_iff`.
3. `toEReal_of_ne_top`: `rw [← WithTop.coe_untop₀_of_ne_top hx]` on the left, `toEReal_coe`.
Decomposition entry: L7.1–L7.6.
#### Mathlib lemmas needed
`WithBot.coe_ne_bot`, `WithBot.coe_le_coe`, `WithBot.coe_lt_coe`, `WithBot.coe_injective`, `Function.Injective.eq_iff`, `WithTop.coe_untop₀_of_ne_top`, `EReal`.
#### Sources
[RM] §2.3.1 (the supporting value as an infimum; plan decision 5 for the `EReal` codomain).
#### Generality decision
Pure order bookkeeping.

### [T040] `supportValue`: lattice bounds, finiteness, monotonicity, admissibility
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T039 · **Parallel**: yes (with T001, T010) · **Type**: def API
- **Leaves**: L7.7–L7.13

#### Statement
```lean
noncomputable def supportValue (h : ℕ → WithTop ℝ) (m : ℝ) : EReal :=
  ⨅ k : ℕ, (toEReal (h k) - ((m * k : ℝ) : EReal))

theorem supportValue_le (h : ℕ → WithTop ℝ) (m : ℝ) (k : ℕ) :
    supportValue h m ≤ toEReal (h k) - ((m * k : ℝ) : EReal) := by sorry

theorem le_supportValue_iff {m : ℝ} {a : EReal} :
    a ≤ supportValue h m ↔ ∀ k, a ≤ toEReal (h k) - ((m * k : ℝ) : EReal) := by sorry

theorem coe_le_supportValue_iff {m y : ℝ} :
    (y : EReal) ≤ supportValue h m ↔ ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ h k := by sorry

theorem supportValue_ne_bot_iff {m : ℝ} :
    supportValue h m ≠ ⊥ ↔ ∃ y : ℝ, ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ h k := by sorry

theorem supportValue_eq_top_iff {m : ℝ} : supportValue h m = ⊤ ↔ ∀ k, h k = ⊤ := by sorry

theorem supportValue_mono {g : ℕ → WithTop ℝ} (hgh : ∀ k, g k ≤ h k) (m : ℝ) :
    supportValue g m ≤ supportValue h m := by sorry

theorem isAdmissible_iff_exists_supportValue_ne_bot :
    IsAdmissible v ↔ ∃ m : ℝ, supportValue v m ≠ ⊥ := by sorry
```
#### Proof sketch
`supportValue h m = ⨅ k, (toEReal (h k) - ↑(m * k))` (no `sorry`).
1. `supportValue_le := iInf_le _ k`; `le_supportValue_iff := le_iInf_iff`.
2. `coe_le_supportValue_iff`: 1, then per `k`: `rcases eq_or_ne (h k) ⊤`: `⊤` gives `toEReal ⊤ - ↑_ = ⊤` (`toEReal_top`, `EReal.top_sub_coe`), `le_top` on both sides; else write `h k = ↑r` (`WithTop.ne_top_iff_exists`), `toEReal_coe`, `← EReal.coe_sub`, `EReal.coe_le_coe_iff`, `le_sub_iff_add_le`, `WithTop.coe_le_coe`.
3. `supportValue_ne_bot_iff`: `EReal.eq_bot_iff_forall_lt` negated: `s ≠ ⊥ ↔ ∃ y : ℝ, ¬ s < ↑y`, i.e. `∃ y, ↑y ≤ s` (`not_lt`); then 2.
4. `supportValue_eq_top_iff`: `iInf_eq_top`; per `k`, `toEReal (h k) - ↑(mk) = ⊤ ↔ h k = ⊤` (`⊤` case by `EReal.top_sub_coe`; finite case: `← EReal.coe_sub`, `EReal.coe_ne_top`).
5. `supportValue_mono`: `iInf_mono fun k ↦ ?_`; `EReal.sub_le_sub (toEReal_le_toEReal.mpr (hgh k)) le_rfl` (if that name is absent at the pin, use `sub_eq_add_neg` on `EReal` and `add_le_add_right`).
6. `isAdmissible_iff_exists_supportValue_ne_bot`: `NewtonPolygon.isAdmissible_iff_exists_line`, 3, `exists_comm`.
Decomposition entry: L7.7–L7.13.
#### Mathlib lemmas needed
`iInf_le`, `le_iInf_iff`, `EReal.top_sub_coe`, `le_top`, `WithTop.ne_top_iff_exists`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `le_sub_iff_add_le`, `WithTop.coe_le_coe`, `EReal.eq_bot_iff_forall_lt`, `not_lt`, `iInf_eq_top`, `EReal.coe_ne_top`, `iInf_mono`, `EReal.sub_le_sub`, `add_le_add_right`, `sub_eq_add_neg`, `NewtonPolygon.isAdmissible_iff_exists_line`, `exists_comm`.
#### Sources
[Ked07] §2 (Q-Ked-vr: "v_r … is the y-intercept of the supporting line of the Newton polygon of slope r"); [RM] §2.3.1–§2.3.2.
#### Generality decision
Generic over `h : ℕ → WithTop ℝ`, any real slope.

### [T041] The points and their polygon have the same supporting value
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T040 · **Parallel**: yes (with T001, T010) · **Type**: theorem
- **Leaves**: L7.14

#### Statement
```lean
theorem supportValue_newtonPolygon (hv : IsAdmissible v) (m : ℝ) :
    supportValue (newtonPolygon v) m = supportValue v m := by sorry
```
#### Proof sketch
`le_antisymm`.
1. `≤`: `supportValue_mono (NewtonPolygon.newtonPolygon_le (exists_isConvexMinorant_iff_isAdmissible.mpr hv)) m`.
2. `≥`: `rcases` on `supportValue v m` being `⊥` (`bot_le`), `⊤`, or `↑r` (`EReal.eq_bot_iff_forall_lt`/`EReal.coe_toReal` — or `induction supportValue v m using EReal.rec`). `⊤`: `supportValue_eq_top_iff` gives `∀ k, v k = ⊤`, so `v = fun _ ↦ ⊤` and `newtonPolygon v = v` (`newtonPolygon_eq_self isConvexSeq_top`), hence equal. `↑r`: `coe_le_supportValue_iff` gives the line `↑(r + mk) ≤ v k`; `(isNewtonPolygonOf_newtonPolygon …).line_le` gives it below the polygon; `coe_le_supportValue_iff` back.
Decomposition entry: L7.14.
#### Mathlib lemmas needed
`NewtonPolygon.newtonPolygon_le`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `EReal.rec`, `bot_le`, `le_antisymm`.
#### Sources
[Ked07] §2 (Q-Ked-vr); [RM] §2.3.1 ("the supporting value is the infimum over k of h k - k·m").
#### Generality decision
Admissible `v`.

### [CLEANUP-15] Run /cleanup on `SupportValue.lean`
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T041 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T042] Attainment at a point of contact; piecewise affinity
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: CLEANUP-15 · **Parallel**: yes (with T001, T010) · **Type**: theorems
- **Leaves**: L7.15–L7.17

#### Statement
```lean
theorem supportValue_eq_of_line_le {n : ℕ} (hn : h n ≠ ⊤) {m : ℝ}
    (hline : ∀ k : ℕ, (((h n).untop₀ + m * ((k : ℝ) - n) : ℝ) : WithTop ℝ) ≤ h k) :
    supportValue h m = toEReal (h n) - ((m * n : ℝ) : EReal) := by sorry

theorem IsConvexSeq.supportValue_eq_of_unitSlope (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {m : ℝ}
    (h₁ : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ m) (h₂ : ∀ j, n ≤ j → (m : WithTop ℝ) ≤ unitSlope h j) :
    supportValue h m = toEReal (h n) - ((m * n : ℝ) : EReal) := by sorry

theorem IsConvexSeq.supportValue_eq_of_unitSlope_le_le (hh : IsConvexSeq h) {j : ℕ}
    (hj : h (j + 1) ≠ ⊤) {m : ℝ} (h₁ : unitSlope h j ≤ m) (h₂ : (m : WithTop ℝ) ≤ unitSlope h (j + 1)) :
    supportValue h m = toEReal (h (j + 1)) - ((m * (j + 1 : ℕ) : ℝ) : EReal) := by sorry
```
#### Proof sketch
1. `supportValue_eq_of_line_le`: `le_antisymm (supportValue_le h m n) (le_iInf fun k ↦ ?_)`: with `h n = ↑η` (`WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`), `hline k` reads `↑(η + m (k - n)) ≤ h k`; if `h k = ⊤` the target is `_ ≤ ⊤ - ↑_ = ⊤`; else `h k = ↑r` and `η - mn ≤ r - mk` (`EReal.coe_sub`, `EReal.coe_le_coe_iff`, `linarith` from `η + m(k - n) ≤ r`).
2. `IsConvexSeq.supportValue_eq_of_unitSlope`: `(NewtonPolygon.IsConvexSeq.line_le_iff hh hn m).mpr ⟨h₁, h₂⟩` gives `hline`; then 1.
3. `IsConvexSeq.supportValue_eq_of_unitSlope_le_le`: apply 2 at `n := j + 1`. `h j ≠ ⊤`: from `h₁`, `unitSlope h j ≠ ⊤` (`ne_top_of_le_ne_top WithTop.coe_ne_top`), `unitSlope_ne_top_iff`. `h₁'`: for `i < j + 1` with `h i ≠ ⊤`, `i ≤ j` and `hh.monotoneOn (mem_finiteSupport.mpr hi) (mem_finiteSupport.mpr hj') hij : unitSlope h i ≤ unitSlope h j ≤ ↑m`. `h₂'`: for `i ≥ j + 1`, if `h i = ⊤` then `unitSlope h i = ⊤ ≥ ↑m` (`unitSlope_eq_top_iff`, `le_top`); else `hh.monotoneOn` from `j + 1` to `i` and `h₂`.
Decomposition entry: L7.15–L7.17.
#### Mathlib lemmas needed
`iInf_le`, `le_iInf`, `WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `EReal.top_sub_coe`, `le_top`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `ne_top_of_le_ne_top`, `WithTop.coe_ne_top`, `NewtonPolygon.unitSlope_ne_top_iff`, `NewtonPolygon.unitSlope_eq_top_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.mem_finiteSupport`, `le_antisymm`.
#### Sources
[Ked07] §2 (Q-Ked-vr); [RM] §0.5.1 (supporting lines), §2.3.4 ("piecewise affine with the unit slopes as its breakpoints").
#### Generality decision
Statement 1 needs no convexity (the hypothesis `hh` was removed at planning); 2–3 need `IsConvexSeq h`.

### [T043] Attainment at the endpoints of the face
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T042 · **Parallel**: yes (with T001, T010) · **Type**: theorems
- **Leaves**: L7.18–L7.20

#### Statement
```lean
theorem IsConvexSeq.supportValue_eq_faceRight (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (m : ℝ) :
    supportValue h m = toEReal (h (faceRight h m)) - ((m * faceRight h m : ℝ) : EReal) := by sorry

theorem IsConvexSeq.supportValue_eq_faceLeft (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (m : ℝ) :
    supportValue h m = toEReal (h (faceLeft h m)) - ((m * faceLeft h m : ℝ) : EReal) := by sorry

theorem IsConvexSeq.supportValue_ne_bot (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (m : ℝ) : supportValue h m ≠ ⊥ := by sorry
```
#### Proof sketch
1. `supportValue_eq_faceRight := supportValue_eq_of_line_le (NewtonPolygon.ne_top_faceRight h0 m) (NewtonPolygon.IsConvexSeq.faceRight_line_le hh h0 hu m)`.
2. `supportValue_eq_faceLeft`: same with `ne_top_faceLeft`, `IsConvexSeq.faceLeft_line_le`.
3. `supportValue_ne_bot`: `rw [hh.supportValue_eq_faceRight h0 hu m, toEReal_of_ne_top (ne_top_faceRight h0 m), ← EReal.coe_sub]`, `EReal.coe_ne_bot`.
Decomposition entry: L7.18–L7.20.
#### Mathlib lemmas needed
`NewtonPolygon.ne_top_faceRight`, `NewtonPolygon.ne_top_faceLeft`, `NewtonPolygon.IsConvexSeq.faceRight_line_le`, `NewtonPolygon.IsConvexSeq.faceLeft_line_le`, `EReal.coe_sub`, `EReal.coe_ne_bot`.
#### Sources
[Ked07] proof of Cor. 2 (Q-Ked-C2); [RM] §2.3.1 ("the attained form"), §0.5.3.
#### Generality decision
Layer 0's face hypotheses: anchored at `0` and `SlopesUnbounded` (Layer 0 decision 5).

### [T044] Attained at a point iff a vertex lies on the supporting line
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T043 · **Parallel**: yes (with T001, T010) · **Type**: theorem
- **Leaves**: L7.21

#### Statement
```lean
theorem IsNewtonPolygonOf.exists_eq_supportValue_iff (hh : IsNewtonPolygonOf v h)
    (hv : ∃ k, v k ≠ ⊤) {m : ℝ} (hs : supportValue v m ≠ ⊥) :
    (∃ k, toEReal (v k) - ((m * k : ℝ) : EReal) = supportValue v m) ↔
      ∃ k, IsVertex h k ∧ toEReal (h k) - ((m * k : ℝ) : EReal) = supportValue v m := by sorry
```
#### Proof sketch
Let `s := supportValue v m`; `s ≠ ⊤` from `hv` (`supportValue_eq_top_iff`), so `s = ↑r` (`EReal.coe_toReal hs' hs`).
(←) `⟨k, hk, heq⟩`: `hh.eq_of_isVertex hk : h k = v k`, rewrite.
(→) `⟨k, hk⟩`. The line `L j := ↑(r + m j)` is below the points (`coe_le_supportValue_iff` at `r`), hence below `h` (`hh.line_le`), and `L k = v k ≥ h k ≥ L k`, so `h k = v k = L k`. Let `F := {j | toEReal (h j) - ↑(m j) = ↑r}` (the polygon's contact set); `k ∈ F`. By `IsConvexSeq.line_le_iff hh.convex (h k ≠ ⊤) m` (→) applied to the line through `(k, h k)` (which is `L`), the unit slopes before `k` (finite) are `≤ m` and those from `k` on are `≥ m`. Let `j₁ := Nat.find ⟨k, hk'⟩` (the least element of `F`). Claim `IsVertex h j₁`: `h j₁ ≠ ⊤` (it is on the line). If `j₁ = anchor h` done (`Or.inl`). Else `anchor h < j₁`, so `h (j₁ - 1) ≠ ⊤` (the finiteness set is an interval, `hh.convex.ordConnected`) and `j₁ - 1 ∉ F` (`Nat.find_min'`), i.e. `h (j₁ - 1)` lies strictly above `L` (it is `≥ L` since `L ≤ h`); hence `unitSlope h (j₁ - 1) = h j₁ - h (j₁ - 1) < L j₁ - L (j₁ - 1) = m`, while `unitSlope h j₁ ≥ m` (`h (j₁ + 1) ≥ L (j₁ + 1)`): `Or.inr` with `WithTop.coe_lt_coe` arithmetic. Finally `toEReal (h j₁) - ↑(m j₁) = ↑r` by `j₁ ∈ F`.
Decomposition entry: L7.21 (two attacks and their repairs are recorded there: the contact set must be the polygon's, not the points', and `hv` is needed).
#### Mathlib lemmas needed
`EReal.coe_toReal`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.IsNewtonPolygonOf.le_points`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsConvexSeq.ordConnected`, `Set.OrdConnected.out`, `NewtonPolygon.IsVertex`, `NewtonPolygon.anchor_le`, `NewtonPolygon.eq_top_of_lt_anchor`, `Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `NewtonPolygon.unitSlope_nat`, `WithTop.coe_lt_coe`, `WithTop.coe_le_coe`, `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `le_antisymm`.
#### Sources
[RM] §2.3.3 ("the Gauss norm is attained at an index exactly when the polygon has a vertex on the supporting line"); [Gou20] p. 254 (Q-Gou-first: "i is the largest integer such that ‖f(X)‖_c = |a_i| c^i").
#### Generality decision
`v` with a point (`hv`) and a finite-from-below supporting value; `h` its polygon.

### [CLEANUP-16] Run /cleanup on `SupportValue.lean`
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T044 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T045] The slopes with finite supporting value form an interval; concavity
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: CLEANUP-16 · **Parallel**: yes (with T001, T010) · **Type**: theorems
- **Leaves**: L7.22–L7.23

#### Statement
```lean
theorem convex_setOf_supportValue_ne_bot : Convex ℝ {m : ℝ | supportValue h m ≠ ⊥} := by sorry

theorem concaveOn_toReal_supportValue :
    ConcaveOn ℝ {m : ℝ | supportValue h m ≠ ⊥} (fun m ↦ (supportValue h m).toReal) := by sorry
```
#### Proof sketch
1. `convex_setOf_supportValue_ne_bot`: `convex_iff_ordConnected.mpr ⟨fun m₁ h₁ m₂ h₂ m hm ↦ ?_⟩`; from `supportValue_ne_bot_iff` get `y₂` with `↑(y₂ + m₂ k) ≤ h k`; then `↑(y₂ + m k) ≤ ↑(y₂ + m₂ k)` since `m ≤ m₂` and `(k : ℝ) ≥ 0` (`mul_le_mul_of_nonneg_right hm.2 (Nat.cast_nonneg k)`, `WithTop.coe_le_coe`), so `supportValue h m ≠ ⊥`.
2. `concaveOn_toReal_supportValue`: `by_cases hall : ∀ k, h k = ⊤`. If so, `supportValue h m = ⊤` for all `m` (`supportValue_eq_top_iff`), `EReal.toReal_top`, `concaveOn_const`. Otherwise fix `k₀` with `h k₀ ≠ ⊤`; on `S := {m | supportValue h m ≠ ⊥}` the value is real. Show `(supportValue h m).toReal = ⨅ k : NewtonPolygon.finiteSupport h, ((h k).untop₀ - m * k)` for `m ∈ S`: both are the greatest lower bound of `{(h k).untop₀ - m k | h k ≠ ⊤}` (use `coe_le_supportValue_iff` and `le_ciInf`/`ciInf_le` with `BddBelow` from `S`; `EReal.coe_toReal`). Then `-(⨅ …) = ⨆ k : finiteSupport h, (m * k - (h k).untop₀)` (`Real.sSup_neg`-style, or prove the identity via `le_antisymm` and `neg_le`), and `convexOn_ciSup` (the root lemma in Layer 0's `ConvexSeq.lean`, `Nonempty (finiteSupport h)` from `k₀`) with each `m ↦ m * k - c` convex (`(convexOn_id _).smul`-style: `ConvexOn.add (convexOn_const _ _)`; a linear function is convex: `LinearMap.convexOn`, or `convexOn_iff_forall_pos` directly) and bounded above on `S` (`bddAbove_def` from the bound `-(supportValue h m).toReal`); finally `neg_convexOn_iff`/`ConcaveOn.neg` and `ConcaveOn.congr`.
Decomposition entry: L7.22–L7.23.
#### Mathlib lemmas needed
`convex_iff_ordConnected`, `Set.OrdConnected`, `mul_le_mul_of_nonneg_right`, `Nat.cast_nonneg`, `WithTop.coe_le_coe`, `EReal.toReal_top`, `concaveOn_const`, `EReal.coe_toReal`, `le_ciInf`, `ciInf_le`, `Real.sSup_neg`, `convexOn_ciSup`, `ConvexOn.add`, `convexOn_const`, `LinearMap.convexOn`, `convexOn_iff_forall_pos`, `neg_convexOn_iff`, `ConcaveOn.neg`, `ConcaveOn.congr`, `bddAbove_def`, `neg_le`.
#### Sources
[Ked07] §2 (Q-Ked-vr: `v_r` is a minimum of affine functions of `r`; "r ↦ v_r(P) is continuous"); [RM] §2.3.4 ("is concave").
#### Generality decision
Any sequence `h` (no convexity): concavity of an infimum of affine functions.

### [T046] The biconjugate: the polygon is the supremum of its supporting lines
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T045 · **Parallel**: yes (with T001, T010) · **Type**: theorem
- **Leaves**: L7.24

#### Statement
```lean
theorem iSup_supportValue_add (hv : IsAdmissible v) (k : ℕ) :
    ⨆ m : ℝ, (supportValue v m + ((m * k : ℝ) : EReal)) = toEReal (newtonPolygon v k) := by sorry
```
#### Proof sketch
Let `h := newtonPolygon v`, `hh := isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.mpr hv)`. `le_antisymm`:
1. `≤`: `iSup_le fun m ↦ ?_`: `supportValue v m ≤ supportValue h m` is an equality (`supportValue_newtonPolygon hv m`); `supportValue h m ≤ toEReal (h k) - ↑(mk)` (`supportValue_le`); add `↑(mk)`: `EReal.sub_add_cancel`-style for a real summand (`toEReal (h k) - ↑r + ↑r = toEReal (h k)`: cases `h k = ⊤` (`EReal.top_sub_coe`, `EReal.top_add_coe`) or finite (`EReal.coe_sub`, `EReal.coe_add`, `sub_add_cancel`)); `add_le_add_right` on `EReal`.
2. `≥`: three cases.
   (i) `h k ≠ ⊤`: choose a supporting slope `σ`: if `h (k+1) ≠ ⊤`, `σ := (unitSlope h k).untop₀`; `IsConvexSeq.line_le_iff hh.convex hk σ` (←) holds (`hh.convex.monotoneOn`: earlier finite unit slopes `≤ unitSlope h k`, later `≥`), so `supportValue h σ = toEReal (h k) - ↑(σ k)` (`IsConvexSeq.supportValue_eq_of_unitSlope`), i.e. `supportValue v σ + ↑(σ k) = toEReal (h k)` (T041 and the cancellation of 1); `le_iSup _ σ`. If `h (k+1) = ⊤` and `anchor h < k`: `σ := (unitSlope h (k-1)).untop₀` (finite by the interval property), same argument (later unit slopes are `⊤`). If `k = anchor h` and `h (k+1) = ⊤` (a single point): any `σ`, `line_le_iff` trivially.
   (ii) `h k = ⊤`, `anchor h ≤ k`, and `v` has a last finite index `d < k` (`h d ≠ ⊤`, `h (d+1) = ⊤`; exists since the finiteness set is an interval not containing `k`): for `m ≥ (unitSlope h (d-1)).untop₀` (or any `m` if `d = anchor`), `supportValue h m = toEReal (h d) - ↑(md)` (T042), so `supportValue v m + ↑(mk) = ↑((h d).untop₀ + m (k - d))`, unbounded in `m` (`k > d`): `EReal.eq_top_iff_forall_lt` and `le_iSup` with `exists_nat_gt`-style choice of `m`.
   (iii) `h k = ⊤`, `k < anchor h =: a`: for `m ≤ (unitSlope h a).untop₀` (if finite; else any `m`), `supportValue h m = toEReal (h a) - ↑(ma)` (`line_le_iff` at `a`: no earlier finite slopes), so the term is `↑((h a).untop₀ + m (k - a))` with `k - a < 0`, unbounded as `m → -∞`.
   The remaining case (`h k = ⊤`, `k ≥ a`, infinite finiteness set) is impossible (`hh.convex.ordConnected`).
Decomposition entry: L7.24 (a worker may split case (i) off as a sub-ticket `exists_supporting_slope`).
#### Mathlib lemmas needed
`iSup_le`, `le_iSup`, `EReal.top_sub_coe`, `EReal.top_add_coe`, `EReal.coe_sub`, `EReal.coe_add`, `sub_add_cancel`, `add_le_add_right`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.IsConvexSeq.ordConnected`, `NewtonPolygon.anchor_le`, `NewtonPolygon.eq_top_of_lt_anchor`, `NewtonPolygon.anchor_mem`, `EReal.eq_top_iff_forall_lt`, `exists_nat_gt`, `WithTop.untop₀`, `WithTop.coe_untop₀_of_ne_top`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`.
#### Sources
[Ked07] §1 (Q-Ked-def: "the intersection of every closed halfplane lying above some nonvertical line containing all the points"); [RM] §2.3.4 ("the polygon and the Gauss norm function determine each other").
#### Generality decision
Admissible `v`; the identity is in `EReal` so that the `⊤` cases are honest.

### [CLEANUP-17] Run /cleanup on `SupportValue.lean`
- **Status**: open · **File**: `SupportValue.lean` · **Depends on**: T046 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T047] The bridge to `Polynomial.gaussNorm`; the term as a power of the base
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: CLEANUP-13, CLEANUP-17 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L8.1–L8.3

#### Statement
```lean
theorem gaussNorm_toAbsoluteValue {c : ℝ} (hc : 0 ≤ c) (f : Polynomial K) :
    f.gaussNorm (toAbsoluteValue K) c = PowerSeries.gaussNorm norm c (f : PowerSeries K) := by sorry

theorem exists_gaussNorm_coe_eq {c : ℝ} (hc : 0 ≤ c) (f : Polynomial K) :
    ∃ k, PowerSeries.gaussNorm norm c (f : PowerSeries K) = ‖f.coeff k‖ * c ^ k := by sorry

theorem norm_coeff_mul_rpow_pow_eq_rpow {k : ℕ} {γ : Γ} (hγ : v (coeff k f) = (γ : WithTop Γ))
    (m : ℝ) : ‖coeff k f‖ * (v.base ^ m) ^ k = v.base ^ (m * k - v.embed γ) := by sorry
```
#### Proof sketch
1. `gaussNorm_toAbsoluteValue`: `(Polynomial.gaussNorm_coe_powerSeries (NormedField.toAbsoluteValue K) f hc).symm` and `⇑(NormedField.toAbsoluteValue K) = norm` (`rfl`; `show` or `simp only [NormedField.toAbsoluteValue]` if needed).
2. `exists_gaussNorm_coe_eq`: `Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue K) c f` gives `k` with `f.gaussNorm _ c = ‖f.coeff k‖ * c ^ k`; rewrite with 1.
3. `norm_coeff_mul_rpow_pow_eq_rpow := v.norm_mul_rpow_pow_eq_rpow hγ m k`.
Decomposition entry: L8.1–L8.3.
#### Mathlib lemmas needed
`Polynomial.gaussNorm_coe_powerSeries`, `NormedField.toAbsoluteValue`, `Polynomial.exists_eq_gaussNorm`.
#### Sources
[RM] convention 11 ("Polynomial.gaussNorm_coe_powerSeries is the bridge"), §2.3.3 ("for a polynomial it is always attained").
#### Generality decision
`0 ≤ c` as in Mathlib.

### [T048] Bounded at `b ^ m` iff the supporting value at `m` is finite
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T047 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L8.4–L8.5

#### Statement
```lean
theorem hasGaussNorm_rpow_iff (m : ℝ) :
    HasGaussNorm norm (v.base ^ m) f ↔ supportValue (coeffVal v f) m ≠ ⊥ := by sorry

theorem hasGaussNorm_iff_supportValue_ne_bot {c : ℝ} (hc : 0 < c) :
    HasGaussNorm norm c f ↔ supportValue (coeffVal v f) (Real.logb v.base c) ≠ ⊥ := by sorry
```
#### Proof sketch
1. `hasGaussNorm_rpow_iff := (hasGaussNorm_rpow_iff_exists_line v m).trans (NewtonPolygon.supportValue_ne_bot_iff).symm` (the two line forms coincide syntactically: `∃ y, ∀ k, ↑(y + m k) ≤ coeffVal v f k`).
2. `hasGaussNorm_iff_supportValue_ne_bot`: `rw [← v.rpow_logb hc]` on the left, then 1.
Decomposition entry: L8.4–L8.5.
#### Mathlib lemmas needed
`Iff.trans`, `Iff.symm`.
#### Sources
[RM] §2.3.2 ("Prove HasGaussNorm norm c f is equivalent to the supporting value being finite").
#### Generality decision
Radius form and slope form.

### [CLEANUP-ALL-3] Run /cleanup-all before milestone M3 (T049)
- **Status**: open · **Depends on**: T048, CLEANUP-13, CLEANUP-17 · **Parallel**: no · **Type**: cleanup
- Sweep before the milestone: `Polynomial.lean`, `SupportValue.lean`, `GaussNorm.lean` so far. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T049] [M3] The Gauss norm is `b ^ (−s)`: infimum, real and polygon forms
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: CLEANUP-ALL-3 · **Parallel**: no · **Type**: theorems · **Milestone**: M3 ([RM] §2.3.1–§2.3.2)
- **Leaves**: L8.6–L8.9

#### Statement
```lean
theorem gaussNorm_rpow_eq_of_supportValue_eq {m s : ℝ} (hs : supportValue (coeffVal v f) m = (s : EReal)) :
    gaussNorm norm (v.base ^ m) f = v.base ^ (-s) := by sorry

theorem gaussNorm_rpow_eq_rpow_neg_toReal {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    gaussNorm norm (v.base ^ m) f = v.base ^ (-(supportValue (coeffVal v f) m).toReal) := by sorry

theorem supportValue_coeffVal_eq_neg_logb {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    supportValue (coeffVal v f) m =
      ((-Real.logb v.base (gaussNorm norm (v.base ^ m) f) : ℝ) : EReal) := by sorry

theorem supportValue_newtonPolygon_eq (hf : IsAdmissible (coeffVal v f)) (m : ℝ) :
    supportValue (newtonPolygon v f) m = supportValue (coeffVal v f) m := by sorry
```
#### Proof sketch
1. `gaussNorm_rpow_eq_of_supportValue_eq` (`hs : supportValue (coeffVal v f) m = ↑s`): `PowerSeries.gaussNorm_eq`; `hbd : HasGaussNorm norm (b^m) f` from T048 (`hs ▸ EReal.coe_ne_bot s`). `le_antisymm`:
   - `ciSup_le fun k ↦ ?_`: if `coeff k f = 0` the term is `0 ≤ b ^ (-s)` (`Real.rpow_nonneg`); else `v (coeff k f) = ↑γ`, `norm_coeff_mul_rpow_pow_eq_rpow`, and `↑s ≤ toEReal (coeffVal v f k) - ↑(mk)` (`supportValue_le`, `hs ▸`) gives `s ≤ e γ - mk` (`EReal.coe_sub`, `EReal.coe_le_coe_iff` after `coeffVal_apply`, `embedTop_coe`, `toEReal_coe`), so `b ^ (mk - eγ) ≤ b ^ (-s)` (`Real.rpow_le_rpow_left_iff v.one_lt_base`, `linarith`).
   - `≥`: `le_of_forall_lt`-style: for `t < b ^ (-s)` write `t < b ^ (-(s+ε))` for some `ε > 0` (continuity of `rpow` in the exponent, or: if `t ≤ 0` trivial since the supremum is `≥ 0`; else `ε := -s - Real.logb b t > 0`), then `↑(s + ε) > supportValue …` so some `k` has `toEReal (coeffVal v f k) - ↑(mk) < ↑(s + ε)` (`iInf_lt_iff`); that `k` has `coeff k f ≠ 0` (else the term is `⊤`), and its term is `b ^ (mk - eγ) > b ^ (-(s+ε)) > t`; `lt_of_lt_of_le _ (le_ciSup hbd k)`.
2. `gaussNorm_rpow_eq_rpow_neg_toReal`: `hs' : supportValue _ m ≠ ⊤` (`supportValue_eq_top_iff` with `exists_coeffVal_ne_top v hf`); `EReal.coe_toReal hs' hs` and 1.
3. `supportValue_coeffVal_eq_neg_logb`: from 2, `Real.logb_rpow v.base_pos v.one_lt_base.ne'`, `neg_neg`, `EReal.coe_toReal`.
4. `supportValue_newtonPolygon_eq := NewtonPolygon.supportValue_newtonPolygon hf m` (T041).
Decomposition entry: L8.6–L8.9 (the sign check of [RM] §2.3.1 is recorded there).
#### Mathlib lemmas needed
`PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `Real.rpow_nonneg`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `EReal.coe_ne_bot`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`, `iInf_lt_iff`, `le_of_forall_lt`, `Real.logb_rpow`, `Real.rpow_logb`, `EReal.coe_toReal`, `NewtonPolygon.supportValue_newtonPolygon`, `neg_neg`, `lt_of_lt_of_le`.
#### Sources
[Ked07] §2 (Q-Ked-vr, multiplicative reading); [RM] §2.3.1 ("gaussNorm norm c f = b ^ (-(the supporting value of the polygon at slope m)) … the Gauss norm is the Legendre transform of the polygon … ⚠ Check the sign against a worked example": `1 − pX`, `m = 2`, Gauss norm `p`, `h 1 − 1·2 = −1`).
#### Generality decision
The infimum form takes the real value `s` as a hypothesis; the `toReal` form takes `s ≠ ⊥` and `f ≠ 0`.

### [CLEANUP-18] Run /cleanup on `GaussNorm.lean`
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T049 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T050] The attained form: the Gauss norm is the term at the face endpoints
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: CLEANUP-18 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L8.10–L8.11

#### Statement
```lean
theorem gaussNorm_rpow_eq_norm_coeff_faceRight (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hu : SlopesUnbounded (newtonPolygon v f)) (m : ℝ) :
    gaussNorm norm (v.base ^ m) f =
      ‖coeff (faceRight (newtonPolygon v f) m) f‖ * (v.base ^ m) ^ faceRight (newtonPolygon v f) m := by sorry

theorem gaussNorm_rpow_eq_norm_coeff_faceLeft (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hu : SlopesUnbounded (newtonPolygon v f)) (m : ℝ) :
    gaussNorm norm (v.base ^ m) f =
      ‖coeff (faceLeft (newtonPolygon v f) m) f‖ * (v.base ^ m) ^ faceLeft (newtonPolygon v f) m := by sorry
```
#### Proof sketch
Let `h := newtonPolygon v f`, convex (T021), `h 0 ≠ ⊤` (`newtonPolygon_zero_eq` + `coeffVal_ne_top_iff`).
1. `faceRight`: `R := faceRight h m`; `IsConvexSeq.supportValue_eq_faceRight (isConvexSeq_newtonPolygon v hf) h0' hu m : supportValue h m = toEReal (h R) - ↑(mR)`; `h R = coeffVal v f R` (`(isNewtonPolygonOf_newtonPolygon v hf).eq_of_faceRight h0' hu m`), finite, so `coeff R f ≠ 0`, `v (coeff R f) = ↑γ`; hence `supportValue (coeffVal v f) m = ↑(e γ - mR)` (T049's polygon form, `toEReal_coe`, `EReal.coe_sub`); `gaussNorm_rpow_eq_of_supportValue_eq` gives `b ^ (-(eγ - mR)) = b ^ (mR - eγ) = ‖coeff R f‖ (b^m)^R` (`norm_coeff_mul_rpow_pow_eq_rpow`, `neg_sub`).
2. `faceLeft`: identical with `supportValue_eq_faceLeft`, `eq_of_faceLeft`.
Decomposition entry: L8.10–L8.11.
#### Mathlib lemmas needed
`NewtonPolygon.IsConvexSeq.supportValue_eq_faceRight`, `NewtonPolygon.IsConvexSeq.supportValue_eq_faceLeft`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceRight`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceLeft`, `EReal.coe_sub`, `neg_sub`, `WithTop.ne_top_iff_exists`.
#### Sources
[Gou20] pp. 258–259 (Q-Gou-second: "the maximum is realized at the degree k term"); [RM] §2.3.1 ("the attained form … which is the one the later layers use").
#### Generality decision
`coeff 0 f ≠ 0` (anchored at `0`) and `SlopesUnbounded` — Layer 0's face hypotheses.

### [T051] The Gauss norm is attained iff a vertex lies on the supporting line
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T050 · **Parallel**: yes (with T063) · **Type**: theorem
- **Leaves**: L8.12

#### Statement
```lean
theorem exists_gaussNorm_rpow_eq_iff {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    (∃ k, gaussNorm norm (v.base ^ m) f = ‖coeff k f‖ * (v.base ^ m) ^ k) ↔
      ∃ k, IsVertex (newtonPolygon v f) k ∧
        toEReal (newtonPolygon v f k) - ((m * k : ℝ) : EReal) = supportValue (coeffVal v f) m := by sorry
```
#### Proof sketch
`hadm : IsAdmissible (coeffVal v f)` from `hs` (`NewtonPolygon.isAdmissible_iff_exists_supportValue_ne_bot`); `hs' : supportValue _ m ≠ ⊤` (`exists_coeffVal_ne_top v hf`); `r := (supportValue _ m).toReal`, `supportValue _ m = ↑r` (`EReal.coe_toReal`); `gaussNorm = b ^ (-r)` (T049).
Per `k`: `gaussNorm = ‖coeff k f‖ (b^m)^k ↔ toEReal (coeffVal v f k) - ↑(mk) = ↑r`: if `coeff k f = 0` both sides are false (`b ^ (-r) > 0` by `Real.rpow_pos_of_pos`, `norm_zero`; `⊤ - ↑_ = ⊤ ≠ ↑r`); else `v (coeff k f) = ↑γ`, `norm_coeff_mul_rpow_pow_eq_rpow`, injectivity of `t ↦ b ^ t` (`Real.rpow_le_rpow_left_iff` both ways / `le_antisymm_iff`), `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `sub_eq_iff_eq_add`, `neg_eq_iff_eq_neg`, `linarith`.
Then `exists_congr` this with `NewtonPolygon.IsNewtonPolygonOf.exists_eq_supportValue_iff (isNewtonPolygonOf_newtonPolygon v hadm) ⟨k₀, _⟩ hs` (T044), rewriting `supportValue` by `↑r` where needed.
Decomposition entry: L8.12.
#### Mathlib lemmas needed
`NewtonPolygon.isAdmissible_iff_exists_supportValue_ne_bot`, `EReal.coe_toReal`, `Real.rpow_pos_of_pos`, `norm_zero`, `Real.rpow_le_rpow_left_iff`, `le_antisymm_iff`, `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `EReal.top_sub_coe`, `EReal.top_ne_coe`, `sub_eq_iff_eq_add`, `exists_congr`, `NewtonPolygon.IsNewtonPolygonOf.exists_eq_supportValue_iff`.
#### Sources
[RM] §2.3.3; [Gou20] p. 254 (Q-Gou-first).
#### Generality decision
`s ≠ ⊥` (bounded) and `f ≠ 0`.

### [T052] `m ↦ −log_b ‖f‖_{b^m}`: concave, piecewise affine, and recovering the polygon
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T051 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L8.13–L8.15

#### Statement
```lean
theorem concaveOn_neg_logb_gaussNorm (hf : f ≠ 0) :
    ConcaveOn ℝ {m : ℝ | HasGaussNorm norm (v.base ^ m) f}
      (fun m ↦ -Real.logb v.base (gaussNorm norm (v.base ^ m) f)) := by sorry

theorem neg_logb_gaussNorm_eq_of_unitSlope_le_le (hf : IsAdmissible (coeffVal v f)) {j : ℕ} {m : ℝ}
    (hj : newtonPolygon v f (j + 1) ≠ ⊤) (h₁ : unitSlope (newtonPolygon v f) j ≤ m)
    (h₂ : (m : WithTop ℝ) ≤ unitSlope (newtonPolygon v f) (j + 1)) :
    -Real.logb v.base (gaussNorm norm (v.base ^ m) f) =
      (newtonPolygon v f (j + 1)).untop₀ - m * (j + 1 : ℕ) := by sorry

theorem toEReal_newtonPolygon_eq_iSup (hf : IsAdmissible (coeffVal v f)) (k : ℕ) :
    toEReal (newtonPolygon v f k) = ⨆ m : ℝ, (supportValue (coeffVal v f) m + ((m * k : ℝ) : EReal)) := by sorry
```
#### Proof sketch
1. `concaveOn_neg_logb_gaussNorm`: `{m | HasGaussNorm norm (b^m) f} = {m | supportValue (coeffVal v f) m ≠ ⊥}` (`Set.ext`, T048); on it `-Real.logb v.base (gaussNorm norm (b^m) f) = (supportValue _ m).toReal` (T049's `supportValue_coeffVal_eq_neg_logb` read backwards: `EReal.toReal_coe`, `neg_neg`); `(NewtonPolygon.concaveOn_toReal_supportValue).congr` (T045).
2. `neg_logb_gaussNorm_eq_of_unitSlope_le_le`: `hf' : f ≠ 0` (from `hj`: `h (j+1) ≠ ⊤` while `newtonPolygon v 0 = ⊤`); `supportValue (coeffVal v f) m = supportValue h m` (T049 polygon form) `= toEReal (h (j+1)) - ↑(m (j+1))` (`IsConvexSeq.supportValue_eq_of_unitSlope_le_le (isConvexSeq_newtonPolygon v hf) hj h₁ h₂`, T042) `= ↑((h (j+1)).untop₀ - m (j+1))` (`toEReal_of_ne_top hj`, `EReal.coe_sub`); then `supportValue_coeffVal_eq_neg_logb` (with `hs` from this real value, `EReal.coe_ne_bot`) and `EReal.coe_eq_coe_iff`; `Nat.cast_succ`.
3. `toEReal_newtonPolygon_eq_iSup := (NewtonPolygon.iSup_supportValue_add hf k).symm` (T046).
Decomposition entry: L8.13–L8.15.
#### Mathlib lemmas needed
`Set.ext`, `EReal.toReal_coe`, `neg_neg`, `ConcaveOn.congr`, `NewtonPolygon.concaveOn_toReal_supportValue`, `NewtonPolygon.IsConvexSeq.supportValue_eq_of_unitSlope_le_le`, `EReal.coe_sub`, `EReal.coe_ne_bot`, `EReal.coe_eq_coe_iff`, `Nat.cast_succ`, `NewtonPolygon.iSup_supportValue_add`.
#### Sources
[RM] §2.3.4 ("m ↦ -log_b (gaussNorm norm (b ^ m) f) is concave and piecewise affine with the unit slopes as its breakpoints — the polygon and the Gauss norm function determine each other"); [Ked07] §1–§2 (Q-Ked-def, Q-Ked-vr).
#### Generality decision
`f ≠ 0` for the concavity statement (the set is otherwise all of `ℝ` with the junk value `0`); admissibility for the other two.

### [CLEANUP-19] Run /cleanup on `GaussNorm.lean`
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T052 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T053] Polynomials: finite supporting value, the attained form
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: CLEANUP-19 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L8.16–L8.17

#### Statement
```lean
theorem supportValue_coeffVal_ne_bot (f : Polynomial K) (m : ℝ) : supportValue (coeffVal v f) m ≠ ⊥ := by sorry

theorem gaussNorm_rpow_eq_norm_coeff_faceRight (h0 : f.coeff 0 ≠ 0) (m : ℝ) :
    PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) =
      ‖f.coeff (faceRight (newtonPolygon v f) m)‖ * (v.base ^ m) ^ faceRight (newtonPolygon v f) m := by sorry
```
#### Proof sketch
1. `supportValue_coeffVal_ne_bot`: `(PowerSeries.hasGaussNorm_rpow_iff v m).mp (hasGaussNorm_coe v (v.base ^ m))` after rewriting `coeffVal_coe`.
2. `gaussNorm_rpow_eq_norm_coeff_faceRight` (polynomial): `rw [← newtonPolygon_coe]`; `PowerSeries.gaussNorm_rpow_eq_norm_coeff_faceRight v hadm h0' hu m` with `hadm` from `isAdmissible_coeffVal v` (through `coeffVal_coe`), `h0'` from `Polynomial.coeff_coe` and `h0`, `hu := slopesUnbounded_newtonPolygon v` (through `newtonPolygon_coe`); finish with `Polynomial.coeff_coe`.
Decomposition entry: L8.16–L8.17.
#### Mathlib lemmas needed
`Polynomial.coeff_coe`.
#### Sources
[RM] §2.3.1, §2.3.3.
#### Generality decision
`coeff 0 f ≠ 0` for the attained form.

### [CLEANUP-20] Run /cleanup on `GaussNorm.lean`
- **Status**: open · **File**: `GaussNorm.lean` · **Depends on**: T053 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T054] Pure series: the line controls the coefficients, the Gauss norm is the constant term
- **Status**: open · **File**: `Pure.lean` · **Depends on**: CLEANUP-20 · **Parallel**: yes (with T063) · **Type**: def API
- **Leaves**: L9.1–L9.3

#### Statement
```lean
def IsPure : Prop := NewtonPolygon.IsPure (newtonPolygon v f) m

def HasFirstBreak (l : ℕ) : Prop := NewtonPolygon.HasFirstBreak (newtonPolygon v f) m l

theorem IsPure.le_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

theorem IsPure.norm_coeff_mul_rpow_pow_le (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) (k : ℕ) : ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖ := by sorry

theorem IsPure.gaussNorm_rpow_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) : gaussNorm norm (v.base ^ m) f = ‖coeff 0 f‖ := by sorry
```
#### Proof sketch
The generator prints both the `PowerSeries` and `Polynomial` definitions of `IsPure`/`HasFirstBreak`; this ticket is the `PowerSeries` API.
1. `IsPure.le_coeffVal`: `h := newtonPolygon v f`, `h 0 = coeffVal v f 0` (`newtonPolygon_zero_eq hf h0`), so `anchor h = 0`. For `k` with `h k ≠ ⊤`: `NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq (a := 0) (k := k)` with `hp.2` (every unit slope `j < k` is finite, since the finiteness set is an interval containing `0` and `k`, hence `= ↑m`) gives `h k = h 0 + k • ↑m`; `newtonPolygon_le hf k` and `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`. For `h k = ⊤`: `coeffVal v f k = ⊤` (`top_le_iff.mp (newtonPolygon_le hf k ▸ le_top)`), `le_top`.
2. `IsPure.norm_coeff_mul_rpow_pow_le`: `v.norm_mul_rpow_pow_le_iff (coeff k f) (coeff 0 f) m k 0` (T005) with `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, and 1.
3. `IsPure.gaussNorm_rpow_eq`: `gaussNorm_eq`; `le_antisymm (ciSup_le (fun k ↦ by simpa using IsPure.norm_coeff_mul_rpow_pow_le …))`; `≥`: `le_ciSup hbd 0` with the term at `0` being `‖coeff 0 f‖` (`pow_zero`, `mul_one`) and `hbd` from 2 (`bddAbove_def`).
Decomposition entry: L9.1–L9.3.
#### Mathlib lemmas needed
`NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq`, `NewtonPolygon.IsPure`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `top_le_iff`, `le_top`, `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, `PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `bddAbove_def`.
#### Sources
[Gou20] Definition 7.4.1 (Q-Gou-D741); [Gou20] p. 254 (Q-Gou-first: "there are no points below the line y = mx"); [RM] §2.4.1.
#### Generality decision
Series with `coeff 0 f ≠ 0` (anchored at `0`) and an admissible sequence.

### [T055] Purity of a genuine series in Gauss-norm terms
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T054 · **Parallel**: yes (with T063) · **Type**: theorem
- **Leaves**: L9.4

#### Statement
```lean
theorem isPure_iff_of_infinite (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hinf : {k | coeff k f ≠ 0}.Infinite) :
    IsPure v f m ↔ (∀ k, ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖) ∧
      ∀ c : ℝ, v.base ^ m < c → ¬ HasGaussNorm norm c f := by sorry
```
#### Proof sketch
`h := newtonPolygon v f`, convex, `h 0 = coeffVal v f 0 ≠ ⊤`. Infinite support: every `h k ≠ ⊤` (if `h k = ⊤` for some `k` then `coeffVal v f j = ⊤` for all `j ≥ k` by `IsConvexSeq.eq_top_of_le` + `newtonPolygon_le`, contradicting `hinf` — `Set.Infinite.exists_gt`).
(→) first clause: T054. Second: for `c > b^m` write `c = b ^ m'` (`v.rpow_logb`), `m' > m` (`Real.rpow_lt_rpow_left_iff`); if `HasGaussNorm norm c f`, T017 gives `y` with `↑(y + m' k) ≤ coeffVal v f k`, hence `≤ h k` (`IsNewtonPolygonOf.line_le`), and `h k = h 0 + k • ↑m` (pure, as in T054); so `y + m' k ≤ η + m k` for all `k` (`WithTop.coe_le_coe`), i.e. `(m' - m) k ≤ η - y`, false for `k` large (`exists_nat_gt`, `linarith`).
(←) `⟨hle, hunb⟩`. The line `L k := ↑(η + m k)` is below the points (`hle` via `v.norm_mul_rpow_pow_le_iff`) hence below `h` (`line_le`), and `L 0 = h 0`. Unit slopes are `≥ m`: if `unitSlope h j < ↑m` for some `j`, by `IsConvexSeq.monotoneOn` all `i ≤ j` have `unitSlope h i < m` and `NewtonPolygon.eq_add_sum_unitSlope` gives `h (j+1) < η + m (j+1) = L (j+1) ≤ h (j+1)`, contradiction. If some unit slope is `> m`, let `j := Nat.find` the least; unit slopes `= m` before `j`, `≥ unitSlope h j` after; pick `m' ∈ (m, (unitSlope h j).untop₀)` (`exists_between`); `IsConvexSeq.line_le_iff hh (hj) m'` (←) holds, so the line of slope `m'` through `(j, h j)` is below `h` hence below the points: `HasGaussNorm norm (b ^ m') f` by T017 (←), with `b ^ m' > b ^ m` (`Real.rpow_lt_rpow_left_iff`), contradicting `hunb`. Hence every unit slope is `m`; one exists (`h 0`, `h 1` finite): `IsPure`.
Decomposition entry: L9.4 (plan D5).
#### Mathlib lemmas needed
`NewtonPolygon.IsConvexSeq.eq_top_of_le`, `Set.Infinite.exists_gt`, `Real.rpow_lt_rpow_left_iff`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `WithTop.coe_le_coe`, `exists_nat_gt`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.eq_add_sum_unitSlope`, `Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `exists_between`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsPure`, `WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`.
#### Sources
[Kob84] IV §4 (Q-Kob-ps, cases (2)–(3)); [Gou20] p. 261 (Q-Gou-ex1); [RM] §2.4.1 corrected (plan D5).
#### Generality decision
Series with infinitely many nonzero coefficients; the polynomial case is T060.

### [T056] The first break: line bounds (`≥` everywhere, `=` at the break, `>` beyond)
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T055 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L9.5–L9.8

#### Statement
```lean
theorem HasFirstBreak.le_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

theorem HasFirstBreak.coeffVal_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) : coeffVal v f l = coeffVal v f 0 + ((m * l : ℝ) : WithTop ℝ) := by sorry

theorem HasFirstBreak.lt_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) {k : ℕ} (hk : l < k) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) < coeffVal v f k := by sorry

theorem HasFirstBreak.coeff_ne_zero (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) : coeff l f ≠ 0 := by sorry
```
#### Proof sketch
`hh := isNewtonPolygonOf_newtonPolygon v hf`; `hb` unfolds to `NewtonPolygon.HasFirstBreak (newtonPolygon v f) m l`; `(hh.hasFirstBreak_iff ⟨0, _⟩ m l).mp hb` gives `0 < l`, (A) `∀ k ≥ anchor h, v (anchor h) + (k - anchor h) • ↑m ≤ coeffVal v f k`, (B) `coeffVal v f (anchor h + l) = coeffVal v f (anchor h) + l • ↑m`, (C) `∃ m' > m, ∀ k ≥ anchor h + l, coeffVal v f (anchor h + l) + (k - (anchor h + l)) • ↑m' ≤ coeffVal v f k`. The anchor is `0`: `hh.anchor_eq_sInf` and `Nat.sInf_eq_zero` with `0 ∈ finiteSupport` (`coeffVal_ne_top_iff.mpr h0`), or `le_antisymm (anchor_le h0') (zero_le _)`.
1. `le_coeffVal k`: (A) at `k` (`zero_le`), `Nat.sub_zero`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`.
2. `coeffVal_eq`: (B) with `zero_add`.
3. `lt_coeffVal hk`: (C) at `k`: `coeffVal v f k ≥ coeffVal v f l + (k - l) • ↑m'`; with (B), `coeffVal v f l = ↑(η + m l)` finite, so the right side is `↑(η + m l + (k - l) m')` and `η + m l + (k - l) m' > η + m k` since `m' > m`, `k > l` (`Nat.cast_sub hk.le`, `mul_lt_mul_of_pos_left`, `linarith`); `lt_of_lt_of_le` with `WithTop.coe_lt_coe`.
4. `coeff_ne_zero`: 2 gives `coeffVal v f l = ↑η + ↑(m l) ≠ ⊤` (`WithTop.add_ne_top`, `WithTop.coe_ne_top`), `coeffVal_ne_top_iff`.
Decomposition entry: L9.5–L9.8 (plan D6).
#### Mathlib lemmas needed
`NewtonPolygon.IsNewtonPolygonOf.hasFirstBreak_iff`, `NewtonPolygon.HasFirstBreak`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq_sInf`, `Nat.sInf_eq_zero`, `NewtonPolygon.anchor_le`, `zero_le`, `Nat.sub_zero`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `zero_add`, `Nat.cast_sub`, `mul_lt_mul_of_pos_left`, `WithTop.coe_lt_coe`, `lt_of_lt_of_le`, `WithTop.add_ne_top`, `WithTop.coe_ne_top`.
#### Sources
[Gou20] p. 254 (Q-Gou-first: "v_p(a_j) ≥ mj for every j … v_p(a_i) = mi … v_p(a_j) > mj if j > i"); [RM] §2.4.2 corrected (plan D6).
#### Generality decision
Series with `coeff 0 f ≠ 0` and an admissible sequence; the break length `l` is Layer 0's.

### [CLEANUP-21] Run /cleanup on `Pure.lean`
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T056 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T057] The first break in Gauss-norm terms
- **Status**: open · **File**: `Pure.lean` · **Depends on**: CLEANUP-21 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L9.9–L9.12

#### Statement
```lean
theorem HasFirstBreak.norm_coeff_mul_rpow_pow_le (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖ := by sorry

theorem HasFirstBreak.norm_coeff_mul_rpow_pow_eq (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) :
    ‖coeff l f‖ * (v.base ^ m) ^ l = ‖coeff 0 f‖ := by sorry

theorem HasFirstBreak.norm_coeff_mul_rpow_pow_lt (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) {k : ℕ} (hk : l < k) :
    ‖coeff k f‖ * (v.base ^ m) ^ k < ‖coeff 0 f‖ := by sorry

theorem HasFirstBreak.gaussNorm_rpow_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    {l : ℕ} (hb : HasFirstBreak v f m l) : gaussNorm norm (v.base ^ m) f = ‖coeff 0 f‖ := by sorry
```
#### Proof sketch
1–3. `v.norm_mul_rpow_pow_le_iff / _eq_iff / _lt_iff (coeff k f) (coeff 0 f) m k 0` (T005) with `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, and T056's `le_coeffVal` / `coeffVal_eq` / `lt_coeffVal` (for `_eq_iff` the right-hand side is `coeffVal v f l = coeffVal v f 0 + ↑(m l)`).
4. `gaussNorm_rpow_eq`: as T054's `IsPure.gaussNorm_rpow_eq` with 1 for the bound and the term at `0`.
Decomposition entry: L9.9–L9.12.
#### Mathlib lemmas needed
`pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, `PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `bddAbove_def`.
#### Sources
[Gou20] p. 254 (Q-Gou-first: "|a_j|(p^m)^j ≤ 1 … = 1 … < 1 if j > i … ‖f(X)‖_c = 1").
#### Generality decision
As T056.

### [T058] Polynomials: purity and first breaks through the coercion; the leading term
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T057 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L9.13–L9.17

#### Statement
```lean
theorem isPure_coe_iff : PowerSeries.IsPure v (f : PowerSeries K) m ↔ IsPure v f m := by sorry

theorem hasFirstBreak_coe_iff {l : ℕ} :
    PowerSeries.HasFirstBreak v (f : PowerSeries K) m l ↔ HasFirstBreak v f m l := by sorry

theorem IsPure.le_coeffVal (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

theorem IsPure.norm_coeff_mul_rpow_pow_le (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) (k : ℕ) :
    ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖ := by sorry

theorem IsPure.norm_coeff_natDegree_mul_rpow_pow_eq (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) :
    ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖ := by sorry
```
#### Proof sketch
1. `isPure_coe_iff`, `hasFirstBreak_coe_iff`: unfold both sides and `rw [newtonPolygon_coe]` (`Iff.rfl`).
2. `IsPure.le_coeffVal`, `IsPure.norm_coeff_mul_rpow_pow_le`: `(isPure_coe_iff v).mpr hp` and the series lemmas (T054) with `hadm` from `isAdmissible_coeffVal v` (via `coeffVal_coe`), `h0` via `Polynomial.coeff_coe`; rewrite `coeffVal_coe`, `Polynomial.coeff_coe`.
3. `IsPure.norm_coeff_natDegree_mul_rpow_pow_eq`: `d := natDegree f`, `f ≠ 0` (`h0`); `h d = coeffVal v f d` (`newtonPolygon_natDegree`), `h 0 = coeffVal v f 0`, and `h d = h 0 + d • ↑m` (`NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq` with `hp.2`: the unit slopes on `[0, d)` are finite (`slopeIndices_newtonPolygon`) hence `= m`); so `coeffVal v f d = coeffVal v f 0 + ↑(m d)`; `v.norm_mul_rpow_pow_eq_iff` at `j = 0` (T005).
Decomposition entry: L9.13–L9.17.
#### Mathlib lemmas needed
`Iff.rfl`, `Polynomial.coeff_coe`, `NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `pow_zero`, `mul_one`.
#### Sources
[Gou20] Definition 7.4.1 and remark (Q-Gou-D741: "|b_n|c^n = 1").
#### Generality decision
`coeff 0 f ≠ 0`.

### [T059] Purity from the bounds (the chord argument)
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T058 · **Parallel**: yes (with T063) · **Type**: theorem
- **Leaves**: L9.18

#### Statement
```lean
theorem isPure_of_bounds (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree)
    (hle : ∀ k, ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖)
    (heq : ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖) : IsPure v f m := by sorry
```
#### Proof sketch
`d := natDegree f`, `η := (coeffVal v f 0).untop₀` (finite by `h0`), `L := (Set.Iic d).piecewise (NewtonPolygon.affineFrom 0 η m) ⊤` (the line through `(0, η)` of slope `m` on `[0, d]`, `⊤` beyond).
1. `L` is convex: `isConvexSeq_affineFrom`, `IsConvexSeq.piecewise_top` with `Set.ordConnected_Iic`.
2. `L ≤ coeffVal v f`: for `k ≤ d`, `↑(η + m k) ≤ coeffVal v f k` is `hle k` through `v.norm_mul_rpow_pow_le_iff … k 0` (T005; `affineFrom_of_le`, `Nat.cast_zero`, `sub_zero`); for `k > d`, `L k = ⊤`? — no: `L k = ⊤` must be `≤ coeffVal v f k`, which holds because `coeff k f = 0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`), `coeffVal_eq_top_iff`.
3. Greatest: for a convex `g ≤ coeffVal v f`: `g 0 ≤ coeffVal v f 0 = L 0`, `g d ≤ coeffVal v f d = L d` (`heq` via `v.norm_mul_rpow_pow_eq_iff … d 0`), and for `0 ≤ k ≤ d`, `IsConvexSeq.le_chord hg (zero_le k) hkd : (d - 0) • g k ≤ (d - k) • g 0 + k • g d ≤ (d - k) • L 0 + k • L d = d • L k` (`WithTop` nsmul arithmetic; `Nat.card_Ico`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, the affine identity `(d - k) η + k (η + m d) = d (η + m k)` by `ring`), so `g k ≤ L k` (`nsmul_le_nsmul_iff_left`-style: divide by `d > 0` — `WithTop.coe_le_coe` after rewriting; `hd : 0 < d`). Beyond `d`, `L k = ⊤`.
4. Hence `IsNewtonPolygonOf (coeffVal v f) L`, so `newtonPolygon v f = L` (`IsNewtonPolygonOf.eq_newtonPolygon`, symm). `IsPure`: unit slopes of `L` on `[0, d)` are `↑m` (`unitSlope_affineFrom`, `Set.piecewise_eq_of_mem`), `⊤` from `d` on; existence from `hd` (`unitSlope L 0 ≠ ⊤`).
Decomposition entry: L9.18. [SRC] `FirstBreak.isPureSeries_of_bounds` is the same argument on the legacy structure. [SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`.
#### Mathlib lemmas needed
`Set.piecewise`, `Set.piecewise_eq_of_mem`, `Set.piecewise_eq_of_notMem`, `Set.ordConnected_Iic`, `NewtonPolygon.affineFrom`, `NewtonPolygon.affineFrom_of_le`, `NewtonPolygon.isConvexSeq_affineFrom`, `NewtonPolygon.unitSlope_affineFrom`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `NewtonPolygon.IsConvexSeq.le_chord`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Nat.card_Ico`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `WithTop.coe_le_coe`, `WithTop.coe_untop₀_of_ne_top`, `NewtonPolygon.IsPure`.
#### Sources
[Gou20] Problem 341 (Q-Gou-D741, ⇐); [RM] §2.4.1.
#### Generality decision
`coeff 0 f ≠ 0`, `0 < natDegree f`; collinear interior points allowed (plan D5).

### [CLEANUP-22] Run /cleanup on `Pure.lean`
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T059 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T060] Purity of a polynomial: the three characterisations
- **Status**: open · **File**: `Pure.lean` · **Depends on**: CLEANUP-22 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L9.19–L9.21

#### Statement
```lean
theorem isPure_iff (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) :
    IsPure v f m ↔ (∀ k, ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖) ∧
      ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖ := by sorry

theorem isPure_iff_gaussNorm (h0 : f.coeff 0 = 1) (hd : 0 < f.natDegree) :
    IsPure v f m ↔
      PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) =
          ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree ∧
        PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) = 1 := by sorry

theorem isPure_iff_hasFirstBreak (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) :
    IsPure v f m ↔ HasFirstBreak v f m f.natDegree := by sorry
```
#### Proof sketch
1. `isPure_iff`: `⟨fun hp ↦ ⟨hp.norm_coeff_mul_rpow_pow_le v h0, hp.norm_coeff_natDegree_mul_rpow_pow_eq v h0⟩, fun ⟨hle, heq⟩ ↦ isPure_of_bounds v h0 hd hle heq⟩` (T058, T059).
2. `isPure_iff_gaussNorm` (`h0 : coeff 0 = 1`): `h0' : f.coeff 0 ≠ 0`; `‖f.coeff 0‖ = 1` (`norm_one`). (→) `IsPure.gaussNorm_rpow_eq` (via `isPure_coe_iff`, T054) gives `gaussNorm = ‖coeff 0‖ = 1`, and `norm_coeff_natDegree_mul_rpow_pow_eq` gives the other. (←) every term `≤ gaussNorm = 1 = ‖coeff 0‖` (`PowerSeries.le_gaussNorm` with `hasGaussNorm_coe`, `Polynomial.coeff_coe`) and `‖coeff d‖ c^d = 1`: `isPure_of_bounds`.
3. `isPure_iff_hasFirstBreak`: `hf : f ≠ 0`; `anchor h = 0` (`anchor_newtonPolygon v hf`, `Polynomial.natTrailingDegree_eq_zero`-style: `natTrailingDegree f = 0` from `h0`, `Polynomial.natTrailingDegree_le_of_ne_zero h0`); `NewtonPolygon.HasFirstBreak` unfolds to `0 < d ∧ (∀ j < d, unitSlope h (0 + j) = ↑m) ∧ unitSlope h (0 + d) ≠ ↑m`; `slopeIndices_newtonPolygon v hf` says the finite unit slopes are exactly `j < d`, and `unitSlope h d = ⊤` (`mem_slopeIndices_iff` negated), `WithTop.top_ne_coe`. Both directions are this bookkeeping (`zero_add`).
Decomposition entry: L9.19–L9.21.
#### Mathlib lemmas needed
`norm_one`, `PowerSeries.le_gaussNorm`, `Polynomial.coeff_coe`, `Polynomial.natTrailingDegree_le_of_ne_zero`, `NewtonPolygon.HasFirstBreak`, `NewtonPolygon.IsPure`, `NewtonPolygon.mem_slopeIndices_iff`, `WithTop.top_ne_coe`, `zero_add`, `Nat.le_zero`.
#### Sources
[Gou20] Problem 341 (Q-Gou-D741); [Gou20] p. 252 (Q-Gou-feat); [RM] §2.4.1.
#### Generality decision
`coeff 0 f ≠ 0` (resp. `= 1`) and `0 < natDegree f`.

### [CLEANUP-23] Run /cleanup on `Pure.lean`
- **Status**: open · **File**: `Pure.lean` · **Depends on**: T060 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T061] Distinguished series: the unit clause is automatic; first break ⟹ distinguished; degree = `faceRight`
- **Status**: open · **File**: `Distinguished.lean` · **Depends on**: CLEANUP-23 · **Parallel**: yes (with T063) · **Type**: theorems
- **Leaves**: L10.1–L10.3

#### Statement
```lean
theorem isMulDistinguished_iff {c : ℝ} {i : ℕ} :
    IsMulDistinguished c f i ↔
      gaussNorm norm c f = ‖coeff i f‖ * c ^ i ∧
        ∀ t, i < t → ‖coeff t f‖ * c ^ t < ‖coeff i f‖ * c ^ i := by sorry

theorem HasFirstBreak.isMulDistinguished (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    {l : ℕ} (hb : HasFirstBreak v f m l) : IsMulDistinguished (v.base ^ m) f l := by sorry

theorem isMulDistinguished_rpow_iff_faceRight_eq (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) (hu : SlopesUnbounded (newtonPolygon v f)) {i : ℕ} :
    IsMulDistinguished (v.base ^ m) f i ↔ faceRight (newtonPolygon v f) m = i := by sorry
```
#### Proof sketch
1. `isMulDistinguished_iff`: (→) `⟨h.gaussNorm_eq, h.gaussTerm_lt⟩`. (←) `⟨?unit, h₁, h₂⟩`: from `h₂ (i+1) (lt_add_one i)` and `mul_nonneg (norm_nonneg _) (pow_nonneg … )` (if `c ^ (i+1) < 0` the inequality still forces `0 < ‖coeff i f‖ * c ^ i`, since the left side is `≥ 0` when `c ≥ 0`; for `c < 0` argue `‖coeff i f‖ ≠ 0` from `h₂` with `i + 2` as well — or simply: `‖coeff i f‖ * c ^ i ≠ 0` because `x < y` with `x = ‖a‖ c^{i+1}` and `y = ‖a_i‖ c^i`, and `y = 0` would need `x < 0`, i.e. `‖coeff (i+1) f‖ c^{i+1} < 0`, impossible when `c ≥ 0`; **state and use `0 ≤ c`? no — the skeleton has no such hypothesis.** Route: if `‖coeff i f‖ = 0` then `y = 0`, and `h₂ (i+1)` reads `‖a_{i+1}‖ c^{i+1} < 0`, while `h₂ (i+2)` reads `‖a_{i+2}‖ c^{i+2} < 0`; multiplying, `c^{i+1}` and `c^{i+2}` are both negative, impossible (`c^{i+2} = c · c^{i+1}` with `c < 0` gives `c^{i+2} > 0`). Simpler: `‖coeff (i+1) f‖ * c ^ (i+1) < 0` and `‖coeff (i+2) f‖ * c ^ (i+2) < 0` force `c^(i+1) < 0` and `c^(i+2) < 0` (`mul_neg_iff`, `norm_nonneg`), but `c ^ (i+2) = c ^ (i+1) * c` and the signs of `c^(i+1)`, `c` cannot both make this negative (`pow_succ`, `mul_neg_iff`, `pow_lt_zero`-free case analysis). Then `coeff i f ≠ 0` (`norm_ne_zero_iff`), `isUnit_iff_ne_zero.mpr`, `IsUnit.isNormMulUnit` ([RAG], `NormMulClass K`).
2. `HasFirstBreak.isMulDistinguished`: `(isMulDistinguished_iff).mpr ⟨_, _⟩`: `gaussNorm = ‖coeff 0 f‖` (T057 `gaussNorm_rpow_eq`) `= ‖coeff l f‖ (b^m)^l` (T057 `norm_coeff_mul_rpow_pow_eq`, symm); for `t > l`, `‖coeff t f‖ (b^m)^t < ‖coeff 0 f‖ = ‖coeff l f‖ (b^m)^l` (T057 `_lt`).
3. `isMulDistinguished_rpow_iff_faceRight_eq`: `R := faceRight h m`, `h := newtonPolygon v f` convex, `h 0 ≠ ⊤`. Facts: (a) `gaussNorm norm (b^m) f = ‖coeff R f‖ (b^m)^R` (T050); (b) for `t > R`: `h t > h R + (t - R) m` (`IsConvexSeq.faceRight_line_lt`), `coeffVal v f t ≥ h t` (`newtonPolygon_le`), `h R = coeffVal v f R` (`eq_of_faceRight`), so `‖coeff t f‖ (b^m)^t < ‖coeff R f‖ (b^m)^R` (`v.norm_mul_rpow_pow_lt_iff`). (←) `rfl ▸ (isMulDistinguished_iff).mpr ⟨a, b⟩`. (→) `hd : IsMulDistinguished (b^m) f i`; `rcases lt_trichotomy i R`: `i < R`: `hd.gaussTerm_lt R hiR : ‖a_R‖c^R < ‖a_i‖c^i = gaussNorm = ‖a_R‖c^R` (`hd.gaussNorm_eq`, (a)), `lt_irrefl`; `R < i`: (b) at `t := i` gives `‖a_i‖c^i < ‖a_R‖c^R = gaussNorm = ‖a_i‖c^i`, `lt_irrefl`; `i = R` ✓.
Decomposition entry: L10.1–L10.3.
#### Mathlib lemmas needed
`PowerSeries.IsMulDistinguished`, `PowerSeries.IsMulDistinguished.gaussNorm_eq`, `PowerSeries.IsMulDistinguished.gaussTerm_lt`, `PowerSeries.IsMulDistinguished.isNormMulUnit_coeff`, `IsUnit.isNormMulUnit`, `isUnit_iff_ne_zero`, `norm_ne_zero_iff`, `mul_neg_iff`, `norm_nonneg`, `pow_succ`, `lt_add_one`, `NewtonPolygon.IsConvexSeq.faceRight_line_lt`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceRight`, `lt_trichotomy`, `lt_irrefl`.
#### Sources
[BGR] 5.2.1/1 (Q-BGR-521: "|g_s| = |g| and |g_s| > |g_ν| for all ν > s"); [Gou20] Proposition 7.2.3 (Q-Gou-P723) and p. 254 (Q-Gou-first: "i is the largest integer such that …"); [Ked07] Cor. 2 proof (Q-Ked-C2); [SRC] `FirstBreak.isMulDistinguished_of_hasFirstBreak`. [SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`.
#### Generality decision
`IsMulDistinguished` over any `NormedCommRing`; here `K` a normed field, where the unit clause is automatic (T061.1 needs no sign hypothesis on `c` — the strict domination of two later terms excludes `c < 0` with `‖coeff i f‖ = 0`). `hu` for the face.

### [CLEANUP-ALL-4] Run /cleanup-all before milestone M4 (T062)
- **Status**: open · **Depends on**: T061, CLEANUP-23 · **Parallel**: no · **Type**: cleanup
- Sweep before the milestone: `Pure.lean`, `Distinguished.lean` so far. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T062] [M4] Polynomials: first break ⟹ distinguished; pure ⟹ distinguished of its degree; degree = `faceRight`
- **Status**: open · **File**: `Distinguished.lean` · **Depends on**: CLEANUP-ALL-4 · **Parallel**: no · **Type**: theorems · **Milestone**: M4 ([RM] §2.4.3)
- **Leaves**: L10.4–L10.6

#### Statement
```lean
theorem HasFirstBreak.isMulDistinguished (h0 : f.coeff 0 ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) l := by sorry

theorem IsPure.isMulDistinguished (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) (hp : IsPure v f m) :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) f.natDegree := by sorry

theorem isMulDistinguished_rpow_iff_faceRight_eq (h0 : f.coeff 0 ≠ 0) {i : ℕ} :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) i ↔
      faceRight (newtonPolygon v f) m = i := by sorry
```
#### Proof sketch
1. `Polynomial.HasFirstBreak.isMulDistinguished`: `(hasFirstBreak_coe_iff v).mpr hb` (T058) and `PowerSeries.HasFirstBreak.isMulDistinguished v hadm h0' hb'` (T061) with `hadm` from `isAdmissible_coeffVal v` via `coeffVal_coe` and `h0'` via `Polynomial.coeff_coe`.
2. `IsPure.isMulDistinguished`: `(isPure_iff_hasFirstBreak v h0 hd).mp hp` (T060) then 1.
3. `Polynomial.isMulDistinguished_rpow_iff_faceRight_eq`: `rw [← newtonPolygon_coe]`; `PowerSeries.isMulDistinguished_rpow_iff_faceRight_eq v hadm h0' (slopesUnbounded_newtonPolygon v …)` (T061) with `newtonPolygon_coe` for the `SlopesUnbounded` hypothesis.
Decomposition entry: L10.4–L10.6.
#### Mathlib lemmas needed
`Polynomial.coeff_coe`.
#### Sources
[RM] §2.4.3 ("a polynomial whose first break is at index i with slope m is distinguished at radius c = b ^ m of degree i, in the sense that its Gauss norm at c is attained at i and nowhere later"); [Gou20] (Q-Gou-first, Q-Gou-P723).
#### Generality decision
`coeff 0 f ≠ 0`; no `SlopesUnbounded` hypothesis for polynomials (automatic).

### [CLEANUP-24] Run /cleanup on `Distinguished.lean`
- **Status**: open · **File**: `Distinguished.lean` · **Depends on**: T062 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T063] `Padic.normedAddValuation`: `v p = 1`, base `p`, the cast embedding
- **Status**: open · **File**: `Padic.lean` · **Depends on**: CLEANUP-3 · **Parallel**: yes (with T016–T062) · **Type**: def API
- **Leaves**: L11.1–L11.6

#### Statement
```lean
noncomputable def normedAddValuation : NormedAddValuation ℚ_[p] ℤ :=
  NormedAddValuation.ofNormAddValZ ℚ_[p] isUniformizer_p

theorem normedAddValuation_apply (x : ℚ_[p]) : normedAddValuation p x = Padic.addValuation x := by sorry

@[simp] theorem normedAddValuation_embed : (normedAddValuation p).embed = Int.castAddHom ℝ := by sorry

theorem normedAddValuation_embed_apply (n : ℤ) : (normedAddValuation p).embed n = n := by sorry

@[simp] theorem normedAddValuation_base : (normedAddValuation p).base = p := by sorry

theorem normedAddValuation_natCast_prime : normedAddValuation p (p : ℚ_[p]) = 1 := by sorry

theorem scale_normedAddValuation_ofNormAddVal :
    (normedAddValuation p).scale (NormedAddValuation.ofNormAddVal ℚ_[p]) = Real.log p := by sorry
```
#### Proof sketch
`normedAddValuation p = ofNormAddValZ ℚ_[p] isUniformizer_p` (no `sorry`).
1. `normedAddValuation_apply`: `show normAddValZ ℚ_[p] x = _` (`ofNormAddValZ_apply`), `NormedField.normAddValZ_padic_apply`.
2. `normedAddValuation_embed := rfl` (`ofNormAddValZ_embed`); `normedAddValuation_embed_apply`: `rw [normedAddValuation_embed]`, `Int.coe_castAddHom` (or `Int.castAddHom` unfolds by `rfl`).
3. `normedAddValuation_base`: `show ‖(p : ℚ_[p])‖⁻¹ = p` (`ofNormAddValZ_base`), `Padic.norm_p`, `inv_inv`.
4. `normedAddValuation_natCast_prime := ofNormAddValZ_apply_isUniformizer ℚ_[p] Padic.isUniformizer_p` (T008).
5. `scale_normedAddValuation_ofNormAddVal`: `scale_ofNormAddValZ_ofNormAddVal ℚ_[p] Padic.isUniformizer_p` (T008) gives `-Real.log ‖(p : ℚ_[p])‖`; `Padic.norm_p`, `Real.log_inv`, `neg_neg`.
Decomposition entry: L11.1–L11.6.
#### Mathlib lemmas needed
`NormedField.normAddValZ_padic_apply`, `Int.coe_castAddHom`, `Padic.norm_p`, `inv_inv`, `Padic.isUniformizer_p`, `Real.log_inv`, `neg_neg`.
#### Sources
[RM] Acceptance ("normAddValZ ℚ_[p] = Padic.addValuation"), Examples ("normAddValZ p = 1 … normAddVal ℚ_[p] is log p times normAddValZ"), §2.2.8.
#### Generality decision
Any prime `p` (`[Fact p.Prime]`).

### [CLEANUP-25] Run /cleanup on `Padic.lean`
- **Status**: open · **File**: `Padic.lean` · **Depends on**: T063 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T064] Examples: `1 − X` (slope `0`) and `1 − pX` (slope `1`)
- **Status**: open · **File**: `Examples.lean` · **Depends on**: CLEANUP-14, CLEANUP-24, CLEANUP-25 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.1–L12.4

#### Statement
```lean
theorem isPure_one_sub_X : IsPure 𝓥 (1 - X : Polynomial ℚ_[p]) 0 := by sorry

theorem newtonSlopes_one_sub_X : newtonSlopes 𝓥 (1 - X : Polynomial ℚ_[p]) = {0} := by sorry

theorem isPure_one_sub_p_mul_X : IsPure 𝓥 (1 - C (p : ℚ_[p]) * X) 1 := by sorry

theorem newtonSlopes_one_sub_p_mul_X : newtonSlopes 𝓥 (1 - C (p : ℚ_[p]) * X) = {1} := by sorry
```
#### Proof sketch
`𝓥 := Padic.normedAddValuation p`, base `p` (T063).
1. `isPure_one_sub_X`: `isPure_of_bounds 𝓥 (h0 : (1 - X).coeff 0 ≠ 0) (hd : 0 < natDegree (1 - X)) hle heq` at `m = 0`: `(𝓥.base) ^ (0:ℝ) = 1` (`Real.rpow_zero`), `one_pow`, `mul_one`. Coefficients: `Polynomial.coeff_sub`, `coeff_one`, `coeff_X` — `coeff 0 = 1`, `coeff 1 = -1`, else `0` (`norm_one`, `norm_neg`, `norm_zero`). `natDegree (1 - X) = 1`: `Polynomial.natDegree_sub_eq_right_of_natDegree_lt` (`natDegree_one`, `natDegree_X`) or `Polynomial.natDegree_X_sub_C`-style after `← neg_sub`, `natDegree_neg`.
2. `newtonSlopes_one_sub_X`: `NewtonPolygon.isPure_iff_slopeMultiset (slopeIndices_newtonPolygon_finite 𝓥) 0 |>.mp` (unfold `IsPure`, `newtonSlopes_def`) gives `slopeMultiset = Multiset.replicate card 0`; `card_newtonSlopes`: `natDegree = 1`, `natTrailingDegree = 0` (`Polynomial.natTrailingDegree_le_of_ne_zero` at index `0`, `Nat.le_zero`); `Multiset.replicate_one`.
3. `isPure_one_sub_p_mul_X`, `newtonSlopes_one_sub_p_mul_X`: as 1–2 with `coeff 1 = -(p : ℚ_[p])` (`Polynomial.coeff_C_mul`, `coeff_X`), `‖-p‖ * (p ^ (1:ℝ)) ^ 1 = p⁻¹ * p = 1` (`norm_neg`, `Padic.norm_p`, `Real.rpow_one`, `pow_one`, `inv_mul_cancel₀`, `Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero`), `natDegree (1 - C p * X) = 1` (`Polynomial.natDegree_C_mul_X` with `p ≠ 0`).
Decomposition entry: L12.1–L12.4.
#### Mathlib lemmas needed
`Real.rpow_zero`, `Real.rpow_one`, `one_pow`, `pow_one`, `mul_one`, `Polynomial.coeff_sub`, `Polynomial.coeff_one`, `Polynomial.coeff_X`, `Polynomial.coeff_C_mul`, `norm_one`, `norm_neg`, `norm_zero`, `Polynomial.natDegree_sub_eq_right_of_natDegree_lt`, `Polynomial.natDegree_one`, `Polynomial.natDegree_X`, `Polynomial.natDegree_C_mul_X`, `NewtonPolygon.isPure_iff_slopeMultiset`, `Multiset.replicate_one`, `Polynomial.natTrailingDegree_le_of_ne_zero`, `Nat.le_zero`, `Padic.norm_p`, `inv_mul_cancel₀`, `Nat.cast_ne_zero`, `Nat.Prime.ne_zero`.
#### Sources
[RM] Examples and Acceptance ("The polygon of 1 - X is the single unit segment of slope 0, and 1 - pX has slope 1").
#### Generality decision
Any prime `p`.

### [T065] Example: `1 + pX + p³X²` has slopes `{1, 2}`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T064 · **Parallel**: no · **Type**: example
- **Leaves**: L12.5

#### Statement
```lean
theorem newtonSlopes_one_add_p_mul_X_add_p_cube_mul_X_sq :
    newtonSlopes 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2) = {1, 2} := by sorry
```
#### Proof sketch
`f := 1 + C p * X + C (p^3) * X^2`. Coefficients: `coeff 0 = 1`, `coeff 1 = p`, `coeff 2 = p^3`, else `0` (`Polynomial.coeff_add`, `coeff_one`, `coeff_C_mul`, `coeff_X`, `coeff_X_pow`; `simp` with `Polynomial.coeff_C_mul_X_pow`). Heights: `coeffVal 𝓥 f = w` with `w := (0, 1, 3, ⊤, …)` (`coeffVal_apply`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply`, `Padic.valuation_one`, `Padic.valuation_p`, `Padic.valuation_pow`, `Padic.normedAddValuation_embed_apply`; `funext`, `match k` on `0, 1, 2, k+3`). `w` is convex: `NewtonPolygon.isConvexSeq_iff_midpoint` or directly `⟨ordConnected of Iic 2, monotoneOn of (1, 2, ⊤, …)⟩` (`unitSlope_nat`, `WithTop` arithmetic), so `newtonPolygon 𝓥 f = w` (`newtonPolygon_def`, `NewtonPolygon.newtonPolygon_eq_self`). `slopeIndices w = {0, 1}` (`mem_slopeIndices_iff`), `slopeMultiset w = {1, 2}`: unfold `slopeMultiset` (`dif_pos`), `Set.Finite.toFinset` of `{0, 1}` is `{0, 1}` (`Set.toFinset_insert`, `Set.toFinset_singleton`), `Multiset.insert_eq_cons`, `Multiset.map_cons`, `Multiset.map_singleton`, `unitSlope_nat`, `WithTop.untop₀_coe`.
Decomposition entry: L12.5.
#### Mathlib lemmas needed
`Polynomial.coeff_add`, `Polynomial.coeff_one`, `Polynomial.coeff_C_mul`, `Polynomial.coeff_X`, `Polynomial.coeff_X_pow`, `Polynomial.coeff_C_mul_X_pow`, `Padic.addValuation.apply`, `Padic.valuation_one`, `Padic.valuation_p`, `Padic.valuation_pow`, `NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.mem_slopeIndices_iff`, `NewtonPolygon.slopeMultiset`, `NewtonPolygon.unitSlope_nat`, `Set.toFinset_insert`, `Set.toFinset_singleton`, `Multiset.insert_eq_cons`, `Multiset.map_cons`, `Multiset.map_singleton`, `WithTop.untop₀_coe`.
#### Sources
[RM] Examples ("1 + pX + p³X² (slopes 1, 2)"), Acceptance.
#### Generality decision
Any prime `p`.

### [T066] Example: the collinear `1 + pX + p²X²`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T065 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.6–L12.8

#### Statement
```lean
theorem newtonPolygon_one_add_p_mul_X_add_p_sq_mul_X_sq_one :
    newtonPolygon 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) 1 =
      coeffVal 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) 1 := by sorry

theorem not_isVertex_one_add_p_mul_X_add_p_sq_mul_X_sq_one :
    ¬ IsVertex (newtonPolygon 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2)) 1 := by sorry

theorem newtonSlopes_one_add_p_mul_X_add_p_sq_mul_X_sq :
    newtonSlopes 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) = {1, 1} := by sorry
```
#### Proof sketch
As T065 with `w := (0, 1, 2, ⊤, …)`, convex (affine on `[0, 2]`), so `newtonPolygon 𝓥 f = coeffVal 𝓥 f` (`newtonPolygon_eq_self`), which gives the first statement at `1`. `IsVertex`: unfold `NewtonPolygon.IsVertex`; `anchor (newtonPolygon 𝓥 f) = 0` (`anchor_newtonPolygon` with `f ≠ 0`; `natTrailingDegree = 0`), so `1 = anchor` is false; `unitSlope w 0 = 1 = unitSlope w 1` (`unitSlope_nat`, `WithTop` arithmetic), `lt_irrefl`. `newtonSlopes = {1, 1}`: as T065 (`Multiset.replicate 2 1` if the `{1, 1}` notation needs `Multiset.insert_eq_cons`, `Multiset.replicate_succ`).
Decomposition entry: L12.6–L12.8.
#### Mathlib lemmas needed
`NewtonPolygon.IsVertex`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.unitSlope_nat`, `lt_irrefl`, `Multiset.insert_eq_cons`, `Multiset.replicate_succ`, `Polynomial.coeff_add`, `Polynomial.coeff_C_mul_X_pow`, `Padic.valuation_pow`.
#### Sources
[RM] Examples ("a polynomial with a collinear interior point"), Acceptance ("its polygon has … points on it that are not vertices, and the slope multiset is nevertheless correct").
#### Generality decision
Any prime `p`.

### [CLEANUP-26] Run /cleanup on `Examples.lean`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T066 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T067] Examples: `Φ_p` is flat; the coefficients of `Φ_p(X + 1)`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: CLEANUP-26 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.11–L12.13

#### Statement
```lean
theorem newtonPolygon_cyclotomic {k : ℕ} (hk : k < p) : newtonPolygon 𝓥 (cyclotomic p ℚ_[p]) k = 0 := by sorry

theorem isPure_cyclotomic : IsPure 𝓥 (cyclotomic p ℚ_[p]) 0 := by sorry

theorem coeff_cyclotomic_comp_X_add_one (i : ℕ) :
    ((cyclotomic p ℚ_[p]).comp (X + 1)).coeff i = (p.choose (i + 1) : ℚ_[p]) := by sorry
```
#### Proof sketch
1. Coefficients of `Φ_p`: `Polynomial.cyclotomic_prime ℚ_[p] p : cyclotomic p ℚ_[p] = ∑ i ∈ range p, X ^ i`; `Polynomial.finset_sum_coeff`, `Polynomial.coeff_X_pow`, `Finset.sum_ite_eq'`, `Finset.mem_range`: `coeff i = if i < p then 1 else 0`. Heights: `0` for `i < p` (`Padic.valuation_one`/`AddValuation.map_one`), `⊤` beyond. The sequence `w := fun k ↦ if k < p then 0 else ⊤` is convex (`IsConvexSeq.piecewise_top isConvexSeq_zero_fun` on `Set.Iio p`, `Set.ordConnected_Iio`; or `isConvexSeq_iff_midpoint`), so `newtonPolygon 𝓥 Φ_p = w` and `newtonPolygon_cyclotomic hk` follows.
2. `isPure_cyclotomic`: unit slopes of `w` are `0` for `k + 1 < p`, `⊤` from `p - 1`; `natDegree Φ_p = p - 1 ≥ 1` (`Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Nat.Prime.one_lt`) — or `isPure_of_bounds` at `m = 0` with all terms `≤ 1` and the leading term `1`.
3. `coeff_cyclotomic_comp_X_add_one`: from `Polynomial.cyclotomic_prime_mul_X_sub_one ℚ_[p] p : Φ_p * (X - 1) = X ^ p - 1`, compose with `X + 1`: `Polynomial.mul_comp`, `sub_comp`, `X_comp`, `one_comp`, `pow_comp`, `add_sub_cancel_right`: `Φ_p.comp (X + 1) * X = (X + 1) ^ p - 1`; apply `Polynomial.coeff_mul_X` at `i + 1`: `coeff (Φ_p.comp (X+1)) i = coeff ((X + 1) ^ p - 1) (i + 1) = p.choose (i + 1) - 0` (`Polynomial.coeff_sub`, `Polynomial.coeff_X_add_one_pow`, `Polynomial.coeff_one`, `Nat.succ_ne_zero`, `sub_zero`).
Decomposition entry: L12.11–L12.13.
#### Mathlib lemmas needed
`Polynomial.cyclotomic_prime`, `Polynomial.finset_sum_coeff`, `Polynomial.coeff_X_pow`, `Finset.sum_ite_eq'`, `Finset.mem_range`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `NewtonPolygon.isConvexSeq_zero_fun`, `Set.ordConnected_Iio`, `NewtonPolygon.newtonPolygon_eq_self`, `Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Nat.Prime.one_lt`, `Polynomial.cyclotomic_prime_mul_X_sub_one`, `Polynomial.mul_comp`, `Polynomial.sub_comp`, `Polynomial.X_comp`, `Polynomial.one_comp`, `Polynomial.pow_comp`, `add_sub_cancel_right`, `Polynomial.coeff_mul_X`, `Polynomial.coeff_sub`, `Polynomial.coeff_X_add_one_pow`, `Polynomial.coeff_one`, `Nat.succ_ne_zero`, `sub_zero`.
#### Sources
[RM] Acceptance ("Φ_p itself has polygon flat at height 0 and all its roots are units"; "Φ_p(X + 1) / p, where Φ_p is the p-th cyclotomic polynomial").
#### Generality decision
Any prime `p` (for `p = 2`, `Φ₂ = X + 1`).

### [T068] Examples: rescaling the `ℚ_p` polygon by `log p`; the pure series `∑ pⁱXⁱ`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T067 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.15–L12.16

#### Statement
```lean
theorem newtonPolygon_ofNormAddVal_eq_scaleHeight (f : Polynomial ℚ_[p]) :
    newtonPolygon (NormedAddValuation.ofNormAddVal ℚ_[p]) f =
      scaleHeight (Real.log p) (newtonPolygon 𝓥 f) := by sorry

theorem isPure_mk_p_pow : IsPure 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ i) 1 := by sorry
```
#### Proof sketch
1. `newtonPolygon_ofNormAddVal_eq_scaleHeight`: `Polynomial.newtonPolygon_eq_scaleHeight 𝓥 (ofNormAddVal ℚ_[p])` (T036) and `Padic.scale_normedAddValuation_ofNormAddVal` (T063).
2. `isPure_mk_p_pow`: `coeffVal 𝓥 (mk fun i ↦ p ^ i) = fun i ↦ ((i : ℝ) : WithTop ℝ)` (`funext`, `coeffVal_apply`, `PowerSeries.coeff_mk`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply` (`p ^ i ≠ 0`), `Padic.valuation_pow`, `Padic.valuation_p`, `mul_one`, `Padic.normedAddValuation_embed_apply`, `Int.cast_natCast`); this is the affine sequence `0 + 1 * i` (`NewtonPolygon.isConvexSeq_affine 0 1`), its own polygon (`NewtonPolygon.newtonPolygon_affine`); unit slopes `1` (`NewtonPolygon.unitSlope_coe`, `Nat.cast_succ`, `add_sub_cancel_left`), all finite: `IsPure` (`NewtonPolygon.IsPure`, `WithTop.coe_ne_top`).
Decomposition entry: L12.15–L12.16.
#### Mathlib lemmas needed
`PowerSeries.coeff_mk`, `Padic.addValuation.apply`, `Padic.valuation_pow`, `Padic.valuation_p`, `Int.cast_natCast`, `NewtonPolygon.isConvexSeq_affine`, `NewtonPolygon.newtonPolygon_affine`, `NewtonPolygon.unitSlope_coe`, `NewtonPolygon.IsPure`, `Nat.cast_succ`, `add_sub_cancel_left`, `WithTop.coe_ne_top`, `pow_ne_zero`.
#### Sources
[RM] §2.2.8 ("the polygon for normAddValZ on ℚ_p is the polygon for normAddVal divided by log p"), Examples ("1 + pX + p²X² + ⋯ (a pure series of slope 1)"); [Gou20] p. 261 (Q-Gou-ex1).
#### Generality decision
Any prime `p`.

### [T069] Example: the entire series `∑ pⁱ² Xⁱ` with unit slopes `1, 3, 5, …`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T068 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.17–L12.21

#### Statement
```lean
theorem isRestricted_mk_p_pow_sq {c : ℝ} (hc : 0 < c) :
    IsRestricted c (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) := by sorry

theorem coeffVal_mk_p_pow_sq :
    coeffVal 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) = fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by sorry

theorem newtonPolygon_mk_p_pow_sq :
    newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) =
      fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by sorry

theorem unitSlope_newtonPolygon_mk_p_pow_sq (j : ℕ) :
    unitSlope (newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2))) j =
      ((2 * j + 1 : ℝ) : WithTop ℝ) := by sorry

theorem slopesUnbounded_newtonPolygon_mk_p_pow_sq :
    SlopesUnbounded (newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2))) := by sorry
```
#### Proof sketch
1. `isRestricted_mk_p_pow_sq`: `PowerSeries.isRestricted_iff'` ([RAG]); terms `‖(p : ℚ_[p]) ^ (i^2)‖ * c ^ i = (p : ℝ) ^ (-(i^2 : ℤ)) * c ^ i` (`PowerSeries.coeff_mk`, `Padic.norm_p_pow`) `= (c / p ^ i) ^ i` (`zpow_neg`, `zpow_natCast`, `pow_mul`, `sq`, `div_pow`, `inv_mul_eq_div`). Choose `N` with `2 * c ≤ p ^ N` (`pow_unbounded_of_one_lt` with `(1 : ℝ) < p`); for `i ≥ N`, `c / p ^ i ≤ 1 / 2` (`div_le_iff₀`, `pow_le_pow_right₀`), so the term is `≤ (1/2) ^ i` (`pow_le_pow_left₀`, `div_nonneg`). `squeeze_zero'` with `Filter.eventually_atTop.mpr ⟨N, _⟩`, `Filter.Eventually.of_forall (fun i ↦ mul_nonneg …)`, and `tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)`.
2. `coeffVal_mk_p_pow_sq`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_mk`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply (pow_ne_zero _ _)`, `Padic.valuation_pow`, `Padic.valuation_p`, `mul_one`, `Padic.normedAddValuation_embed_apply`, `Int.cast_natCast`, `Nat.cast_pow`.
3. `newtonPolygon_mk_p_pow_sq`: `newtonPolygon_def`, 2, `NewtonPolygon.newtonPolygon_sq` ([L0] Examples).
4. `unitSlope_newtonPolygon_mk_p_pow_sq`: 3 and `NewtonPolygon.unitSlope_sq` (or `unitSlope_newtonPolygon_sq`).
5. `slopesUnbounded_newtonPolygon_mk_p_pow_sq`: `NewtonPolygon.SlopesUnbounded`; given `σ`, `exists_nat_gt σ` gives `j` with `σ < 2 j + 1`; 4 and `WithTop.coe_lt_coe`. (Or `slopesUnbounded_newtonPolygon_of_forall_isRestricted` with 1.)
Decomposition entry: L12.17–L12.21.
#### Mathlib lemmas needed
`PowerSeries.isRestricted_iff'`, `PowerSeries.coeff_mk`, `Padic.norm_p_pow`, `zpow_neg`, `zpow_natCast`, `pow_mul`, `sq`, `div_pow`, `inv_mul_eq_div`, `pow_unbounded_of_one_lt`, `div_le_iff₀`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `div_nonneg`, `squeeze_zero'`, `Filter.eventually_atTop`, `Filter.Eventually.of_forall`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Padic.addValuation.apply`, `Padic.valuation_pow`, `Padic.valuation_p`, `Int.cast_natCast`, `Nat.cast_pow`, `NewtonPolygon.newtonPolygon_sq`, `NewtonPolygon.unitSlope_sq`, `NewtonPolygon.unitSlope_newtonPolygon_sq`, `NewtonPolygon.SlopesUnbounded`, `exists_nat_gt`, `WithTop.coe_lt_coe`, `pow_ne_zero`, `Nat.one_lt_cast`.
#### Sources
[RM] Examples ("∑ pⁱ² Xⁱ, an entire series with unit slopes 1, 3, 5, …"), Acceptance; [L0] Examples (`newtonPolygon_sq`).
#### Generality decision
Any prime `p`; every positive radius for restrictedness.

### [CLEANUP-27] Run /cleanup on `Examples.lean`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T069 · **Parallel**: no · **Type**: cleanup
- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.

### [T070] Example: bounded but not restricted at radius `1`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: CLEANUP-27 · **Parallel**: no · **Type**: examples
- **Leaves**: L12.22–L12.23

#### Statement
```lean
theorem hasGaussNorm_one_mk_ite :
    HasGaussNorm norm 1 (mk fun i : ℕ ↦ if i = 0 then (1 : ℚ_[p]) else (p : ℚ_[p])) := by sorry

theorem not_isRestricted_one_mk_ite :
    ¬ IsRestricted 1 (mk fun i : ℕ ↦ if i = 0 then (1 : ℚ_[p]) else (p : ℚ_[p])) := by sorry
```
#### Proof sketch
`f := mk fun i ↦ if i = 0 then 1 else p`; terms at radius `1`: `‖coeff i f‖ * 1 ^ i = ‖coeff i f‖` (`one_pow`, `mul_one`, `PowerSeries.coeff_mk`).
1. `hasGaussNorm_one_mk_ite`: `HasGaussNorm` is `BddAbove (Set.range …)`; `bddAbove_def.mpr ⟨1, _⟩`: `split_ifs`; `norm_one` or `Padic.norm_p` with `(p : ℝ)⁻¹ ≤ 1` (`inv_le_one_of_one_le₀`, `Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le`).
2. `not_isRestricted_one_mk_ite`: `PowerSeries.isRestricted_iff'` ([RAG]); suppose `Tendsto (fun i ↦ ‖coeff i f‖ * 1 ^ i) atTop (𝓝 0)`; the sequence is eventually the constant `(p : ℝ)⁻¹` (`Filter.eventually_atTop.mpr ⟨1, fun i hi ↦ by simp [coeff_mk, Nat.pos_iff_ne_zero.mp hi, Padic.norm_p]⟩`), so by `Filter.Tendsto.congr'` the constant tends to `0`, and `tendsto_nhds_unique (tendsto_const_nhds) _` gives `(p : ℝ)⁻¹ = 0`, contradicting `inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)` (`ne_of_gt`).
Decomposition entry: L12.22–L12.23.
#### Mathlib lemmas needed
`PowerSeries.HasGaussNorm`, `bddAbove_def`, `PowerSeries.coeff_mk`, `one_pow`, `mul_one`, `norm_one`, `Padic.norm_p`, `inv_le_one_of_one_le₀`, `Nat.one_le_cast`, `Nat.Prime.one_lt`, `PowerSeries.isRestricted_iff'`, `Filter.eventually_atTop`, `Filter.Tendsto.congr'`, `tendsto_nhds_unique`, `tendsto_const_nhds`, `inv_pos`, `Nat.cast_pos`, `Nat.Prime.pos`, `Nat.pos_iff_ne_zero`, `ne_of_gt`.
#### Sources
[RM] §2.3.2 ("These are not the same condition … give the example separating them"); [Gou20] p. 262 (Q-Gou-ex2: "if |x| = 1, then the series does not converge").
#### Generality decision
Any prime `p`.

### [CLEANUP-ALL-5] Run /cleanup-all before milestone M5 (T071)
- **Status**: open · **Depends on**: T070, CLEANUP-14, CLEANUP-24, CLEANUP-25 · **Parallel**: no · **Type**: cleanup
- Sweep before the milestone: `Extension.lean`, `Padic.lean`, `Examples.lean` so far. Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.

### [T071] [M5] Acceptance: `1 + 3^{2j+1}X²` pure of slope `j + ½`; `Φ_p(X+1)/p` pure of slope `−1/(p−1)`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: CLEANUP-ALL-5 · **Parallel**: no · **Type**: examples · **Milestone**: M5 ([RM] Acceptance examples)
- **Leaves**: L12.9–L12.10, L12.14

#### Statement
```lean
theorem isPure_one_add_three_pow_mul_X_sq (j : ℕ) :
    IsPure (Padic.normedAddValuation 3) (1 + C ((3 : ℚ_[3]) ^ (2 * j + 1)) * X ^ 2)
      ((j : ℝ) + 1 / 2) := by sorry

theorem newtonSlopes_one_add_three_pow_mul_X_sq (j : ℕ) :
    newtonSlopes (Padic.normedAddValuation 3) (1 + C ((3 : ℚ_[3]) ^ (2 * j + 1)) * X ^ 2) =
      Multiset.replicate 2 ((j : ℝ) + 1 / 2) := by sorry

theorem isPure_C_inv_mul_cyclotomic_comp_X_add_one :
    IsPure 𝓥 (C ((p : ℚ_[p])⁻¹) * (cyclotomic p ℚ_[p]).comp (X + 1)) (-1 / ((p : ℝ) - 1)) := by sorry
```
#### Proof sketch
1. `isPure_one_add_three_pow_mul_X_sq`: `isPure_of_bounds (Padic.normedAddValuation 3)` (`Nat.fact_prime_three`) at `m := (j : ℝ) + 1/2`. `coeff 0 = 1 ≠ 0`; `natDegree = 2` (`Polynomial.natDegree_add_eq_right_of_natDegree_lt`, `natDegree_one`, `Polynomial.natDegree_C_mul_X_pow` with `(3 : ℚ_[3]) ^ (2j+1) ≠ 0`); coefficients `1`, `0`, `3 ^ (2j+1)` (`Polynomial.coeff_add`, `coeff_one`, `coeff_C_mul_X_pow`). Bounds with `c := (3 : ℝ) ^ m` (`Padic.normedAddValuation_base`): `k = 0`: `1 ≤ 1`; `k = 1`: `0 ≤ 1`; `k = 2`: `‖3 ^ (2j+1)‖ * c ^ 2 = 3 ^ (-(2j+1 : ℤ)) * 3 ^ (2 m) = 1` (`Padic.norm_p_pow`, `← Real.rpow_natCast`, `← Real.rpow_mul`, `← Real.rpow_intCast`, `← Real.rpow_add`, `(2 * j + 1 : ℝ) = m * 2` by `ring`, `Real.rpow_zero`); `k ≥ 3`: `0 ≤ 1`. `heq` is the `k = 2` computation.
2. `newtonSlopes_one_add_three_pow_mul_X_sq`: `NewtonPolygon.isPure_iff_slopeMultiset` with 1 and `card_newtonSlopes = 2 - 0` (`natTrailingDegree = 0` from `coeff 0 = 1`).
3. `isPure_C_inv_mul_cyclotomic_comp_X_add_one`: `g := C (p⁻¹) * Φ_p.comp (X + 1)`, `coeff g i = p⁻¹ * p.choose (i + 1)` (`Polynomial.coeff_C_mul`, T067). `isPure_of_bounds 𝓥` at `m := -1 / ((p : ℝ) - 1)`, `c := (p : ℝ) ^ m`: `coeff g 0 = p⁻¹ * p = 1 ≠ 0` (`Nat.choose_one_right`, `inv_mul_cancel₀`); `natDegree g = p - 1` (`Polynomial.natDegree_C_mul (inv_ne_zero …)`, `Polynomial.natDegree_comp`, `natDegree_cyclotomic`, `Nat.totient_prime`, `natDegree_X_add_C`, `mul_one`), `0 < p - 1` (`Nat.Prime.one_lt`, `Nat.sub_pos_of_lt`). Bounds: for `i + 1 < p`, `i ≥ 1`: `p ∣ p.choose (i + 1)` (`Nat.Prime.dvd_choose_self (Fact.out) (Nat.succ_ne_zero i) hlt`), so `‖(p.choose (i+1) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(1 : ℤ))` (`Padic.norm_int_le_pow_iff_dvd` with `Int.natCast_dvd_natCast`, `pow_one`, `Nat.cast_pow`), hence `‖coeff g i‖ = p * ‖choose‖ ≤ 1` (`norm_mul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `zpow_neg_one`) and `c ^ i = p ^ (m i) ≤ 1` (`Real.rpow_le_one_of_one_le_of_nonpos`, `m ≤ 0`); `i = p - 1`: `‖coeff g (p-1)‖ = p` (`Nat.choose_self`, `norm_one`) and `c ^ (p-1) = p ^ (m (p - 1)) = p ^ (-1 : ℝ) = p⁻¹` (`← Real.rpow_natCast`, `← Real.rpow_mul`, `div_mul_cancel₀` with `(p : ℝ) - 1 ≠ 0`, `Real.rpow_neg_one`), product `1` (`mul_inv_cancel₀`); `i ≥ p`: `coeff g i = 0` (`Nat.choose_eq_zero_of_lt`), term `0 ≤ 1`.
Decomposition entry: L12.9–L12.10, L12.14 (plan D10).
#### Mathlib lemmas needed
`Nat.fact_prime_three`, `Polynomial.natDegree_add_eq_right_of_natDegree_lt`, `Polynomial.natDegree_one`, `Polynomial.natDegree_C_mul_X_pow`, `Polynomial.coeff_add`, `Polynomial.coeff_one`, `Polynomial.coeff_C_mul_X_pow`, `Padic.norm_p_pow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_intCast`, `Real.rpow_add`, `Real.rpow_zero`, `NewtonPolygon.isPure_iff_slopeMultiset`, `Polynomial.coeff_C_mul`, `Nat.choose_one_right`, `Nat.choose_self`, `Nat.choose_eq_zero_of_lt`, `inv_mul_cancel₀`, `mul_inv_cancel₀`, `Polynomial.natDegree_C_mul`, `Polynomial.natDegree_comp`, `Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Polynomial.natDegree_X_add_C`, `Nat.Prime.one_lt`, `Nat.sub_pos_of_lt`, `Nat.Prime.dvd_choose_self`, `Nat.succ_ne_zero`, `Padic.norm_int_le_pow_iff_dvd`, `Int.natCast_dvd_natCast`, `norm_mul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `zpow_neg_one`, `Real.rpow_le_one_of_one_le_of_nonpos`, `div_mul_cancel₀`, `Real.rpow_neg_one`, `norm_one`, `Nat.cast_pow`.
#### Sources
[RM] Acceptance ("1 + 3^{2j+1} X² over ℚ_3 is pure of slope j + ½, as an equality of rational numbers … This is the shape of statement the additive normalisation exists for"; "Φ_p(X + 1) / p is pure of slope -1/(p-1)").
#### Generality decision
The slope is the real `j + 1/2` (resp. `-1/(p-1)`); rationality in general is T033 (plan D10). Only divisibility of the interior binomials is needed.

### [CLEANUP-28] Run /cleanup on `Examples.lean`
- **Status**: open · **File**: `Examples.lean` · **Depends on**: T071 · **Parallel**: no · **Type**: cleanup
- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.

### [T072] Chain-root gate and the roadmap status paragraph
- **Status**: open · **File**: `PhD/TauCeti.lean` · **Depends on**: CLEANUP-3, CLEANUP-5, CLEANUP-7, CLEANUP-10, CLEANUP-13, CLEANUP-14, CLEANUP-17, CLEANUP-20, CLEANUP-23, CLEANUP-24, CLEANUP-25, CLEANUP-28 · **Parallel**: no · **Type**: gate
- **Leaves**: all

#### Statement
```lean
-- PhD/TauCeti.lean already imports PhD.TauCeti.Code.NewtonPolygons.Coeff.Examples (added 2026-10-06).
-- Gate: `lake build PhD.TauCeti` succeeds with no `sorry` warning from PhD/TauCeti/Code/NewtonPolygons/Coeff/;
-- `#print axioms` on the five milestone declarations and on every declaration of the layer reports only
-- `propext`, `Classical.choice`, `Quot.sound`; `lake exe runLinter` is clean on the twelve modules.
```
#### Proof sketch
1. `lake build PhD.TauCeti` (the chain root, both chains in one environment) — must succeed with no `sorry` warnings from `Coeff/`.
2. `#print axioms` on every declaration of the twelve modules (generate the list from `scratch/fullnames.json` as Layer 1's `axioms.py` did); only `propext`, `Classical.choice`, `Quot.sound`.
3. `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>` for the twelve modules.
4. Append the Layer 2 "Status (date)" paragraph to `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md` after the Layer 2 introduction, in the style of Layer 1's: implementation path, the five milestones with their axiom report, and the deviations/errata D1–D10 of `plan.md` (in particular that §2.4.4 is deferred to Layer 3/4, that §2.2.4's direction is corrected, and that restrictedness/distinguishedness come from the rigid-analytic chain's `Restricted/PowerSeries/` files). Do not edit the roadmap's own sentences.
#### Mathlib lemmas needed
(none)
#### Sources
[RM] (the roadmap README).
#### Generality decision
(n/a)

### [CLEANUP-FINAL] Run /cleanup-all on the whole layer
- **Status**: open · **Depends on**: T072 · **Parallel**: no · **Type**: cleanup
- Run /cleanup-all on the twelve modules of `PhD/TauCeti/Code/NewtonPolygons/Coeff/` inline as the main agent: `lake exe runLinter` on each, `lake build PhD.TauCeti` with no warnings from the layer, docstrings naming the final declarations, imports pruned by hand (the build confirms each removal), `#print axioms` standard throughout. Then update the memory file `tauceti-np-layer2-board.md` to COMPLETE and the `parallel-ticket-boards` pointer.
