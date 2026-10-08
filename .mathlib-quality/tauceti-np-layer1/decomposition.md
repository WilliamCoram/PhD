# Decomposition: Newton polygons, Layer 1 (additive valuations of a nonarchimedean field)

Companion to `plan.md`. Every leaf below is a declaration of the skeleton, stated with `sorry`; the
pointer is `File.lean · declaration name` (names are stable, line numbers are not;
`scratch/sorries.py` prints the current line of every open declaration, `scratch/signatures.txt`
their elaborated signatures). Sources, cited by tag as in `plan.md`:

- **[RM]** the roadmap `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1, cited by clause
  (§1.1.1 … §1.5.5); for the definitional clauses of §1.1–§1.4 the roadmap *is* the specification
  and is quoted verbatim;
- **[Kob84]** Koblitz, text layer `references/koblitz.txt` (locator = PDF page, marked
  `===== PDFPAGE N =====`; book page = PDF page − 13);
- **[Gou20]** Gouvêa, text layer `references/gouvea.txt` (book page = PDF page − 3); the pages used
  are also collected in `references/gouvea-6.8-and-3.1.txt`;
- **[BGR]** Bosch–Güntzer–Remmert, read by eye from renders of the scan (PDF page = book page + 8);
  quotes are transcriptions;
- **[Mathlib]** the pinned Mathlib `bbc4475e`; **[PR]** mathlib4#43578 and #43580 (their diffs);
- **[SRC]** the sorry-free `PhD/Main/ForMathlib/…` files listed in `plan.md`, read-only.

Discharge lines (D) name the lemmas a worker will call; every Mathlib name was elaborated against
the pin (`scratch/names_pre.lean` at planning time, `scratch/names_tickets_mathlib.lean` from the
tickets). Attack categories: **[1]** counterexample search, **[2]** edge cases, **[3]** hypothesis
strength, **[4]** source drift, **[5]** discharge, **[6]** composition (internal nodes).

## Skeleton location

`PhD/TauCeti/Code/NewtonPolygons/AddVal/{NegLog, RatLog, Basic, RankOne, Commensurable, Discrete,
Normed, Padic, LaurentSeries, Extension, PadicComplex, Examples}.lean` — 12 files, 144 open
declarations, 152 `sorry`s (every proof; the data of every `def` is written out, as in [SRC] and
[PR]). Gate: `lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples` →
`Build completed successfully (2884 jobs)`, `sorry` warnings only (2026-10-06, after the D1 repair
below). The chain root `PhD/TauCeti.lean` imports the leaf.

## Prior-B2 consultation (Step 4.6), once for the whole tree

All B2 logs under `.mathlib-quality/` were read: the default log (Newton-polygon structure
defects, LWX theta defects), `jacobs`, `lwx-*` (12 boards), `newton-product`, `tate-riesz`,
`tauceti-of-layer0`, `tauceti-rag-layer1`; `tauceti-np-layer0` has no log. **No leaf matches by
name** (no prior board developed additive valuations). The defect *shapes* were applied to every
leaf:

| Prior defect shape | Log entry | Where it was tested here | Outcome |
|---|---|---|---|
| section variable dropped from the elaborated statement | `tauceti-of-layer0` T023, `tauceti-rag-layer1` T004/T014/T016/T022/T059 | every declaration, by reading `scratch/signatures.txt` (143 entries, 0 errors) | **one hit**, repaired (D1 below): the `instance isCommensurable_algebraMap` had lost `[CompleteSpace K] [Algebra.IsAlgebraic K L]` (an instance is a `def`; a `sorry` body uses no section hypothesis). Every other theorem carries its sections' instances; the `def`s `orderAddIsoWithTop` and `AddCommGroup.ratLog` currently omit `[IsOrderedAddMonoid M]`, which their proofs will use and which Lean will then include — the intended final signature, and the one every consumer already assumes |
| statement generalised beyond the source's hypotheses | default log C3 | every leaf more general than its source: `[Ring R]` instead of fields (§1.1–§1.4), arbitrary `K` instead of `𝔽_q` (Laurent series), any normed algebra field instead of the spectral norm (§1.5.1–§1.5.2), no finiteness in §1.3.6 | each re-derived by hand below ([3] attacks); no hit — the proofs in [SRC] already work over rings, `norm_algebraMap'` needs no finiteness, and `NormedAlgebra.norm_eq_spectralNorm` is Mathlib's statement at that generality |
| normalisation silently assumed (`‖p‖ = 1/p`) | `lwx-seam-m` X-4 | L7.*, L10.* (`ℚ_p`, `ℂ_p`): `Padic.norm_p`, `PadicComplex.norm_extends'` are Mathlib theorems | clean |
| unconstrained parameter | `lwx-theta` T-AG1a, `jacobs` J015 | the base `e` of the discrete norm recovery (L5.15, L6.14: `e ≠ 0` and a hypothesis pinning `e`), the exponent `n` of the workhorse (`0 < n`), the ramification index `e` of §1.3.6 (pinned by `he`) | clean; every free scalar is pinned by an explicit hypothesis |
| junk values | `jacobs` W001–W003 | `⊤` at `0` for every additive valuation (`*_eq_top`, `*_zero` leaves), `WithZero.negLog 0 = ⊤` (not the junk `log 0 = 0`), `ratCoeff` read off a chosen witness (`ratCoeff_eq` shows independence) | clean; each junk case is a leaf |
| the instance in the statement is not the expected one | `tauceti-of-layer0` T039 | `Valued.v` on `ℂ_[p]` (`valuedCompletion`) versus `NormedField.valuation` (`‖·‖₊`): L10.3 proves them equal; `Valued.v` on `K⸨X⸩` versus `(idealX K).valuation` (`LaurentSeries.valuation_def` is `rfl`) | clean, both seams are leaves |

## Statement defects found by the adversarial pass (all repaired in the skeleton)

| # | Declaration | Defect | Repair |
|---|---|---|---|
| D1 | `NormedField.isCommensurable_algebraMap` (and, for uniformity, `norm_pow_natDegree_minpoly`, `normAddValQ_algebraMap`) | the section hypotheses `[CompleteSpace K] [Algebra.IsAlgebraic K L]` were dropped from the instance: as elaborated it claimed that *every* ultrametric normed `K`-algebra field inherits commensurability — false (the completion of `K(T)` for the norm with `‖T‖ = p^{√2}` is an ultrametric normed `ℚ_p`-algebra field whose value group `p^{ℤ + √2 ℤ}` is not commensurable with `p`) | the two hypotheses are explicit binders of the three declarations |

No other defect was found; the attacks that produced "no flaw" are recorded per leaf.

## Statement-shape check (gate condition 7)

`scratch/sorries.json` was scanned for `∧` in conclusions. The only conjunctions are inside
shared-witness existentials, which are the allowed shape: `exists_zpow_eq_and_addValQ`
(`∃ m n, 0 < n ∧ v x ^ n = v π ^ m ∧ addValQ = m / n` — the three facts share the witnesses `m, n`),
`exists_normAddVal_eq_and_norm_eq_exp_neg` (`∃ r, normAddVal K x = r ∧ ‖x‖ = exp (-r)`),
`exists_normAddValZ_algebraMap_eq` (`∃ e, 0 < e ∧ normAddValZ L (algebraMap π) = e`),
`exists_normAddValQ_eq` (`∃ x, x ≠ 0 ∧ normAddValQ x = q`), and the field
`exists_zpow_eq` of the class `IsCommensurable` (a definition, not a leaf). Every multi-part
roadmap clause ("prove `negLog_mul`, `negLog_one`, …", "`addValZ v x = k ↔ …`, with `⊤` exactly at
`v x = 0`") is one declaration per part.

---

## Result R1 — the dictionary `Valuation R Mᵐ⁰ → AddValuation R (WithTop M)` (§1.1)

### Plain-English proof (source: [RM] §1.1.1–§1.1.5, [PR], [BGR] 1.5.2)

The multiplicative-additive dictionary is [BGR] 1.5.2: a map `| | = α^ν` with `0 < α < 1` is a
valuation iff `ν(x) = ∞ ⇔ x = 0` and `ν(xy) = ν(x) + ν(y)`. Mathlib has the multiplicative side
(`Valuation R Γ₀`) and a bijection `Valuation.toAddValuation : Valuation R Γ₀ ≃ AddValuation R
(Additive Γ₀)ᵒᵈ` whose codomain is a type synonym. For `Γ₀ = Mᵐ⁰ = WithZero (Multiplicative M)`
the synonym `(Additive Mᵐ⁰)ᵒᵈ` is *isomorphic as an ordered additive monoid* to `WithTop M`: send
`0` to `⊤` and `exp m` to `-m` (this is `negLog`; negation turns the reversed order into the usual
one, and `0 ↦ ⊤` replaces the junk `log 0 = 0`). The isomorphism `orderAddIsoWithTop` is checked
field by field on the two constructors of `WithZero` and the two of `WithTop`. Composing
`toAddValuation` with it gives `addVal`, whose values are literally `negLog (v x)`; the
characterisation `addVal x = m ↔ v x = exp (-m)` is `negLog_eq_coe`, and `addVal x = ⊤ ↔ v x = 0`
is `negLog_eq_top`. Functoriality: an additive hom `f : M →+ N` gives a monoid-with-zero hom
`mapAddHom' f : Mᵐ⁰ →*₀ Nᵐ⁰` (Mathlib's `WithZero.map'` of `f.toMultiplicative`), strictly monotone
when `f` is, and `negLog (mapAddHom' f x) = WithTop.map f (negLog x)` by the same two-case check;
hence `(v.map (mapAddHom' f)).addVal = WithTop.map f ∘ v.addVal`. Finally every valuation `v :
Valuation R Γ₀` restricts to its value group (`v.restrict : Valuation R (ValueGroup₀ v)`, with
`ValueGroup₀ v = (Additive (valueGroup v))ᵐ⁰` definitionally), so `addValValueGroup := addVal
v.restrict` is a tautological additive valuation with values in `WithTop (Additive (valueGroup v))`.

Source structure: [RM] §1.1 is five numbered clauses; clause 1 = L1.1–L1.10, clause 2 = L1.11–L1.13,
clause 3 = L1.14–L1.17, clause 4 = L1.18–L1.20 (+ `addVal_map` L1.17), clause 5 is the architecture
rule obeyed by every later definition. [SRC] `WithZero.lean` and `AddVal/Basic.lean` prove all of it
(sorry-free) with the old names.

### Shared quotes

> **Q1.1** [RM] §1.1.1: "Define `WithZero.negLog : Mᵐ⁰ → WithTop M`, sending `0 ↦ ⊤` and
> `exp m ↦ -m`: the `WithZero.log` of Mathlib's `Mᵐ⁰` API in its additive-valuation reading,
> recording `0` as a genuine `⊤` instead of the junk value `log 0 = 0`, and negated so that the
> reversed order on `Mᵐ⁰` becomes the usual order on `WithTop M`. Prove it underlies an
> order-and-additive isomorphism `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`,
> and prove `negLog_mul`, `negLog_one`, `negLog_eq_top`, `negLog_le_negLog`, and the characterisation
> `negLog x = m ↔ x = exp (-m)`."

> **Q1.2** [RM] §1.1.2: "Define the functoriality `WithZero.mapAddHom' : (M →+ N) → (Mᵐ⁰ →*₀ Nᵐ⁰)`,
> prove it is strictly monotone when the hom is, and prove `negLog` is natural along it."

> **Q1.3** [RM] §1.1.3: "Define `Valuation.addVal : Valuation R Mᵐ⁰ → AddValuation R (WithTop M)` as
> `x ↦ negLog (v x)`, by composing `Valuation.toAddValuation` with the isomorphism of clause 1.
> Prove `addVal_eq_top : v.addVal x = ⊤ ↔ v x = 0` and `addVal_eq_coe : v.addVal x = m ↔ v x =
> exp (-m)`. ⚠ The second is the lemma the rest of Layer 1 runs on".

> **Q1.4** [RM] §1.1.4: "Define `Valuation.addValValueGroup`, the tautological additive valuation of
> an arbitrary valuation, with values in `WithTop` of its own value group written additively. Prove
> `Valuation.addVal_map`: pushing `v` along `mapAddHom' f` pushes `v.addVal` along `f`."

> **Q1.5** [BGR] 1.5.2, p. 42: "If `ν` is a filtration of a ring `A` and if `| | = α^ν`, where
> `0 < α < 1`, is a corresponding semi-norm, then `| |` is a valuation if and only if `ν` satisfies
> the following conditions: (∗) `ν(x) = ∞ ⇔ x = 0`, `x ∈ A`, (∗∗) `ν(xy) = ν(x) + ν(y)`,
> `x, y ∈ A`."

> **Q1.6** [PR] #43578 declaration list (diff read 2026-10-06): `WithZero.negLog`, `negLog_zero`,
> `negLog_exp`, `negLog_eq_top`, `negLog_one`, `negLog_eq_coe`, `negLog_mul`, `negLog_le_negLog`,
> `orderAddIsoWithTop`, `orderAddIsoWithTop_apply`, `mapAddHom'`, `mapAddHom'_exp`,
> `mapAddHom'_strictMono`, `negLog_mapAddHom'`; #43580: `Valuation.addVal`, `addVal_apply :
> v.addVal x = negLog (v x)`, `addVal_eq_coe`, `addVal_map : (v.map (mapAddHom' f) …).addVal x =
> WithTop.map f (v.addVal x)`, `addValValueGroup`, `addValValueGroup_apply : v.addValValueGroup x =
> negLog (v.restrict x)`.

### Leaves

- **L1.1** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_zero` — `negLog 0 = ⊤`.
  Source Q1.1/Q1.6 ("sending `0 ↦ ⊤`"). Match: literal. D: `rfl` (`expRecOn_zero` is definitional).
  [SRC] `WithZero.negLog_zero`.
  Attacks: [2] `M` trivial: `negLog 0 = ⊤` still (both sides are `⊤` of `WithTop PUnit`) ✓; [4] the
  PR states exactly `negLog (0 : Mᵐ⁰) = ⊤` ✓; [5] `rfl` compiles in [SRC] against the same
  definition ✓. SURVIVED.
- **L1.2** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_exp` — `negLog (exp m) = ↑(-m)`.
  Source Q1.1 ("`exp m ↦ -m`"). D: `rfl` (`expRecOn_exp`). [SRC] `negLog_exp`.
  Attacks: [2] `m = 0`: `↑(-0) = ↑0 = 0` consistent with L1.4 ✓; [3] no hypothesis to weaken ✓;
  [5] `rfl` in [SRC] ✓. SURVIVED.
- **L1.3** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_eq_top` — `negLog x = ⊤ ↔ x = 0`.
  Source Q1.1 ("`negLog_eq_top`"), Q1.5 (∗). D: `induction x using expRecOn <;> simp
  [-WithTop.LinearOrderedAddCommGroup.coe_neg]` ([SRC] `negLog_eq_top`; the simp-lemma exclusion is
  the recorded trap: `coe_neg` would rewrite `↑(-m)` to `-↑m`, which is not `⊤`).
  Attacks: [1] `lean_loogle`-style search for `negLog _ = ⊤` contradictions: none (new constant);
  [2] `x = 0` both sides true; `x = exp m`: `↑(-m) ≠ ⊤` (`WithTop.coe_ne_top`) and `exp m ≠ 0` ✓;
  [5] the two-case induction with `simp` compiles in [SRC] ✓. SURVIVED.
- **L1.4** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_one` — `negLog 1 = 0`.
  Source Q1.1 ("`negLog_one`"). D: `rw [← exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]`.
  Attacks: [2] trivial `M` ✓; [4] matches PR ✓; [5] `exp_zero : exp 0 = 1` is `rfl` in Mathlib ✓.
  SURVIVED.
- **L1.5** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_eq_coe` — `negLog x = ↑m ↔ x = exp (-m)`.
  Source Q1.1 ("the characterisation `negLog x = m ↔ x = exp (-m)`"). D: `induction x using
  expRecOn`; zero case: both sides false (`WithTop.top_ne_coe`, `exp_ne_zero`); exp case:
  `rw [negLog_exp, WithTop.coe_inj, exp_inj, neg_eq_iff_eq_neg]` ([SRC] `negLog_eq_coe`).
  Attacks: [2] `m = 0`: `negLog x = 0 ↔ x = exp 0 = 1` consistent with L1.4 ✓; [3] no hypothesis;
  the statement is an `↔`, both directions used downstream (`addVal_eq_coe`) ✓; [5] four Mathlib
  names elaborate (`names_pre.lean`) ✓. SURVIVED.
- **L1.6** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_mul` — `negLog (x * y) = negLog x + negLog y`.
  Source Q1.1 ("`negLog_mul`"), Q1.5 (∗∗). D: double `expRecOn` induction; zero cases by `simp`
  (`⊤ + _ = ⊤`); `rw [← exp_add, negLog_exp ×3, neg_add, WithTop.coe_add]` ([SRC]).
  Attacks: [2] `x = 0`: `⊤ = ⊤ + negLog y` ✓ (`WithTop.top_add`); `y = 0` symmetric ✓; [4] (∗∗) of
  Q1.5 is exactly additivity ✓; [5] `exp_add : exp (a + b) = exp a * exp b` is `rfl` ✓. SURVIVED.
- **L1.7** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_le_negLog` — `negLog x ≤ negLog y ↔ y ≤ x`.
  Source Q1.1 ("`negLog_le_negLog`"). D: double induction; `rw [negLog_exp, negLog_exp,
  WithTop.coe_le_coe, neg_le_neg_iff, exp_le_exp]`; zero cases `simp` (`le_top`, `zero_le'`) ([SRC]).
  Attacks: [2] `x = 0`: `⊤ ≤ negLog y ↔ y ≤ 0` — `negLog y = ⊤ ↔ y = 0`, and `y ≤ 0 ↔ y = 0` ✓;
  `y = 0`: `negLog x ≤ ⊤ ↔ 0 ≤ x`, both true ✓; [3] needs `[LinearOrder M] [IsOrderedAddMonoid M]`
  for `exp_le_exp`: these are the section's instances ✓ (signature line 10); [5] `exp_le_exp`
  elaborates ✓. SURVIVED.
- **L1.8** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_lt_negLog` — strict version. New API (not
  in [PR]); used by nothing yet, kept for the strict order on values. D: `lt_iff_lt_of_le_iff_le`
  from L1.7, or the same induction with `exp_lt_exp`.
  Attacks: [2] as L1.7 ✓; [3] same instances ✓; [5] `lt_iff_lt_of_le_iff_le` (Mathlib) ✓. SURVIVED.
- **L1.9** (leaf, Mathlib) `NegLog.lean · WithZero.orderAddIsoWithTop` (four `sorry` fields) —
  `toFun = negLog`, `invFun = recTopCoe 0 (exp ∘ neg)`. Source Q1.1 ("underlies an
  order-and-additive isomorphism"). D: `left_inv`: `expRecOn` (zero: `rfl`; exp: `exp (- -a) = exp
  a` by `neg_neg`); `right_inv`: `WithTop.recTopCoe` (top: `rfl`; coe: `negLog (exp (-m)) = ↑m` by
  `negLog_exp, neg_neg`); `map_add' := negLog_mul`; `map_le_map_iff' := negLog_le_negLog` ([SRC]
  `negLogOrderAddIso`).
  Attacks: [2] `M` trivial: both sides one-element-plus-top, `recTopCoe` fine ✓; [3] the def
  currently elaborates without `[IsOrderedAddMonoid M]` (signature line 14); the proofs will use
  it (L1.7) and Lean will include it — the PR's signature has it, every consumer has it ✓;
  [5] `(Additive Mᵐ⁰)ᵒᵈ → Mᵐ⁰` is the identity on terms, so `toFun x := negLog x` elaborates (it
  does: the skeleton builds) ✓. SURVIVED.
- **L1.10** (leaf, Mathlib) `NegLog.lean · WithZero.orderAddIsoWithTop_apply` — `orderAddIsoWithTop
  M x = negLog x`. Source Q1.6. D: `rfl`. Attacks: [4] PR has exactly this `@[simp]` lemma ✓;
  [5] `rfl` ✓; [2] n/a (definitional). SURVIVED.
- **L1.11** (leaf, Mathlib) `NegLog.lean · WithZero.mapAddHom'_exp` — `mapAddHom' f (exp m) = exp
  (f m)`. Source Q1.2, Q1.6. D: `rfl` (`WithZero.map'_coe`). Attacks: [2] `f = 0`: `exp 0 = 1` ✓;
  [5] `map'_coe` elaborates ✓; [4] PR ✓. SURVIVED.
- **L1.12** (leaf, Mathlib) `NegLog.lean · WithZero.mapAddHom'_strictMono` — `StrictMono f →
  StrictMono (mapAddHom' f)`. Source Q1.2 ("strictly monotone when the hom is"). D:
  `WithZero.map'_strictMono fun _ _ h ↦ hf h` ([SRC] `expMap_strictMono`).
  Attacks: [3] only `[Preorder M] [Preorder N]` needed — the skeleton states exactly those
  (signature line 21) ✓; [2] constant `f` is not strictly monotone unless `M` is a subsingleton,
  in which case both sides hold ✓; [5] `WithZero.map'_strictMono` elaborates ✓. SURVIVED.
- **L1.13** (leaf, Mathlib) `NegLog.lean · WithZero.negLog_mapAddHom'` — `negLog (mapAddHom' f x) =
  WithTop.map f (negLog x)`. Source Q1.2 ("`negLog` is natural along it"). D: `expRecOn`; zero:
  `rfl` (`map_zero`, `WithTop.map_top`); exp: `rw [mapAddHom'_exp, negLog_exp, negLog_exp,
  WithTop.map_coe, map_neg]` ([SRC] `negLog_expMap`).
  Attacks: [2] `x = 0`: `negLog 0 = ⊤ = WithTop.map f ⊤` ✓; [4] "natural" = this square ✓;
  [5] `WithTop.map_coe`, `map_neg` ✓. SURVIVED.
- **L1.14** (leaf, Mathlib) `Basic.lean · Valuation.addVal_apply` — `v.addVal x = negLog (v x)`.
  Source Q1.3 ("as `x ↦ negLog (v x)`"). D: `rfl` ([SRC]). Attacks: [5] the `rfl` depends on
  `orderAddIsoWithTop`'s `toFun` reducing — it is `negLog` syntactically ✓ (and the def's `rfl`
  for `f ⊤ = ⊤` already type-checks in the skeleton); [4] PR `addVal_apply` ✓; [2] n/a. SURVIVED.
- **L1.15** (leaf, project) `Basic.lean · Valuation.addVal_eq_top` — `v.addVal x = ⊤ ↔ v x = 0`.
  Source Q1.3. D: `rw [addVal_apply, negLog_eq_top]` (L1.14, L1.3).
  Attacks: [2] `x = 0`: `v 0 = 0` so both sides true ✓; [4] exact clause ✓; [5] two project
  leaves ✓. SURVIVED.
- **L1.16** (leaf, project) `Basic.lean · Valuation.addVal_eq_coe` — `v.addVal x = ↑m ↔ v x = exp (-m)`.
  Source Q1.3 ("the lemma the rest of Layer 1 runs on"). D: `addVal_apply ▸ negLog_eq_coe` (L1.5).
  Attacks: [2] `m = 0`: `v.addVal x = 0 ↔ v x = 1` ✓ (units of the valuation); [3] none;
  [5] L1.5 ✓. SURVIVED.
- **L1.17** (leaf, project) `Basic.lean · Valuation.addVal_le_addVal` — order reversal. New API.
  D: `rw [addVal_apply, addVal_apply, negLog_le_negLog]` (L1.7).
  Attacks: [2] `y = 0`: `v.addVal x ≤ ⊤ ↔ 0 ≤ v x`, both true ✓; [4] convention 6 of [RM]
  ("larger slope means larger root") is this reversal ✓; [5] L1.7 ✓. SURVIVED.
- **L1.18** (leaf, project) `Basic.lean · Valuation.addVal_map` — `(v.map (mapAddHom' f) _).addVal x
  = WithTop.map f (v.addVal x)`. Source Q1.4, Q1.6. D: `negLog_mapAddHom' f (v x)` (L1.13), after
  `addVal_apply` and `Valuation.map_apply` (`rfl`) ([SRC] `addVal_map`).
  Attacks: [3] `hf : StrictMono f` is only used to form the `Monotone` argument of `Valuation.map`;
  the equation itself holds for any `f` — the stronger hypothesis is forced by the shape of
  `Valuation.map` (it needs monotonicity) and matches the PR ✓; [2] `v x = 0`: both sides `⊤` ✓;
  [5] L1.13 ✓. SURVIVED.
- **L1.19** (leaf, Mathlib) `Basic.lean · Valuation.addValValueGroup_apply` — `= negLog (v.restrict
  x)`. Source Q1.4, Q1.6. D: `rfl`. Attacks: [5] `ValueGroup₀ v ≡ (Additive (valueGroup v))ᵐ⁰`
  definitionally — the skeleton's `addVal (M := Additive (valueGroup (.ofClass v))) v.restrict`
  elaborates ✓; [4] PR ✓; [2] n/a. SURVIVED.
- **L1.20** (leaf, project) `Basic.lean · Valuation.addValValueGroup_eq_top` — `↔ v x = 0`. New API.
  D: `addValValueGroup_apply`, `negLog_eq_top`, `Valuation.restrict_eq_zero_iff`.
  Attacks: [2] `x = 0` ✓; [5] `restrict_eq_zero_iff` elaborates ✓; [3] none. SURVIVED.

### Internal node R1 (composition attack [6])

Could L1.1–L1.20 hold and the dictionary fail? The dictionary is the *definition* `addVal` plus
L1.14–L1.16, L1.18; the only composition is `toAddValuation ∘ orderAddIsoWithTop`, and
`toAddValuation v x = v x` on terms (type synonym), so `addVal_apply` is `rfl` and everything else
is a property of `negLog`. No gap. SURVIVED.

---

## Result R2 — the `ℚ`-valued logarithm of a rank-one group (`RatLog.lean`, §1.4.2's substrate)

### Plain-English proof (source: [RM] §1.4.2, expanded; [Gou20] 3.1.3 for the classical analogue)

Let `M` be a linearly ordered abelian group and `a₀ < 0` an element such that every `a ∈ M` is
commensurable with `a₀`: `n • a = m • a₀` for some integers `m, n` with `n > 0`. Define
`ratCoeff a := m / n` for a chosen witness. It is well defined: if `n • a = m • a₀` and `n' • a =
m' • a₀` with `n, n' > 0` then `(n' m − n m') • a₀ = n' • (n • a) − n • (n' • a) = 0`, and `M` is
torsion-free (ordered), so `n' m = n m'`, i.e. `m/n = m'/n'`. Set `ratLog a := −ratCoeff a`.
It is additive: from witnesses for `a` and `b`, `(n₁n₂) • (a + b) = (n₂m₁ + n₁m₂) • a₀`, and
`(n₂m₁ + n₁m₂)/(n₁n₂) = m₁/n₁ + m₂/n₂`. It sends `a₀` to `−1` (witness `1 • a₀ = 1 • a₀`). It is
strictly monotone: if `a > 0` with witness `n • a = m • a₀`, then `m • a₀ = n • a > 0` forces `m < 0`
(as `a₀ < 0`), so `ratLog a = −m/n > 0`; apply this to `b − a`. Uniqueness: if `g : M →+ ℚ` has
`g a₀ = −1`, then `n • g a = g (n • a) = g (m • a₀) = −m`, so `g a = −m/n = ratLog a`.
Classical analogue ([Gou20] Prop. 3.1.3 (iv)): two equivalent absolute values differ by a power
`|x|₁ = |x|₂^α`; here the "power" is pinned to `1` by the normalisation at `a₀`.

### Shared quotes

> **Q2.1** [RM] §1.4.2: "Define `Valuation.ratLog v π`, the unique additive hom from the additively
> written value group to `ℚ` sending `v π` to `-1`, and prove it strictly monotone."

> **Q2.2** [RM] convention 3: "an embedding of a dense subgroup of `ℚ` into `ℚ` is unique only up to
> a positive rational scalar, so a data class would hide a normalisation, and two such instances on
> the same field would disagree by a scalar".

> **Q2.3** [Gou20] Prop. 3.1.3, p. 55 (`gouvea.txt`, PDFPAGE 60): "(iii) For any x ∈ k we have
> |x|₁ < 1 if and only if |x|₂ < 1. (iv) There exists a positive real number α such that for every
> x ∈ k we have |x|₁ = |x|₂^α."

### Leaves

- **L2.1** (leaf, Mathlib) `RatLog.lean · AddCommGroup.ratCoeff_eq` (private) — any witness computes
  `ratCoeff h a = m / n`. Source: the well-definedness paragraph above (Q2.1 "the unique additive
  hom" presupposes it). D: `(h a).choose_spec`, the `calc` of [SRC] `ratCoeff_eq` through
  `mul_smul`, `sub_smul`, `IsAddTorsionFree.zsmul_eq_zero_iff_left ha₀`, `div_eq_div_iff`.
  Attacks: [3] `ha₀ : a₀ ≠ 0` is necessary: for `a₀ = 0` every `a` with torsion… every `n • a =
  m • 0 = 0` has solutions only for `a = 0` and then `m` is arbitrary, so `ratCoeff` is not
  well defined — the hypothesis is exactly right ✓; [2] `a = 0`: witnesses `(0, 1)` and `(0, 2)`
  give `0` ✓; [5] `IsAddTorsionFree` for an ordered group is a Mathlib instance
  (`IsOrderedAddMonoid` → `IsAddTorsionFree`), used in [SRC] ✓. SURVIVED.
- **L2.2** (leaf, project) `RatLog.lean · AddCommGroup.ratLog` (`map_zero'`, `map_add'`). Source
  Q2.1. D: `map_zero'`: `ratCoeff_eq … (m := 0) (n := 1)`; `map_add'`: the witness
  `(n₁ n₂) • (a + b) = (n₂ m₁ + n₁ m₂) • a₀` by `smul_add, add_smul, mul_smul`, then three
  `ratCoeff_eq`, `push_cast`, `field_simp`, `ring` ([SRC]).
  Attacks: [2] `a₀` itself: `ratLog a₀ = −1` (L2.4) ✓; [3] `ha₀ : a₀ < 0` only enters through
  `ha₀.ne`; the sign is used in L2.5 — keeping `a₀ < 0` (rather than `≠ 0`) in the definition's
  hypothesis is what makes `ratLog` monotone *increasing*, the sign convention [RM] fixes ✓;
  [5] `field_simp`/`ring` on `(n₂ m₁ + n₁ m₂)/(n₁ n₂) = m₁/n₁ + m₂/n₂` with `n₁ n₂ ≠ 0` ✓.
  SURVIVED.
- **L2.3** (leaf, project) `RatLog.lean · AddCommGroup.ratLog_eq` — `ratLog a = −(m/n)`. D:
  `congrArg Neg.neg (ratCoeff_eq …)`. Attacks: [5] L2.1 ✓; [2] `m = 0` gives `0` ✓; [3] none
  beyond L2.1. SURVIVED.
- **L2.4** (leaf, project) `RatLog.lean · AddCommGroup.ratLog_self` — `ratLog a₀ = −1`. Source
  Q2.1 ("sending `v π` to `-1`"). D: `ratLog_eq (m := 1) (n := 1)`, `norm_num`.
  Attacks: [4] the roadmap's `-1` (so that `addValQ π = +1` after the order reversal of `negLog`)
  — sign checked against `addValQ_self` downstream ✓; [5] ✓; [2] n/a. SURVIVED.
- **L2.5** (leaf, project) `RatLog.lean · AddCommGroup.ratLog_strictMono`. Source Q2.1 ("prove it
  strictly monotone"). D: the positivity lemma `0 < a → 0 < ratLog a` (trichotomy on `m` with
  `zsmul_lt_zsmul_iff_left`), then `map_sub` and `linarith` ([SRC]).
  Attacks: [1] a counter-model would be a non-torsion-free or non-linearly-ordered `M`; the
  instances exclude both ✓; [2] `M = ℤ`, `a₀ = −1`: `ratLog = id` ✓; `a₀ = −2`: `ratLog a = a/2` ✓;
  [3] `IsOrderedAddMonoid` needed for `zsmul_lt_zsmul_iff_left` ✓ present. SURVIVED.
- **L2.6** (leaf, project) `RatLog.lean · AddCommGroup.ratLog_unique` — `g a₀ = −1 → g = ratLog`.
  New (the substrate of [RM] §1.4.4). D: `AddMonoidHom.ext`; for `a` take the witness, `n • g a =
  g (n • a) = g (m • a₀) = m • g a₀ = −m` (`map_zsmul`), so `g a = −m/n = ratLog a` by L2.3 and
  `eq_div_iff`.
  Attacks: [1] uniqueness fails without commensurability (two independent generators admit two
  homs) — the hypothesis `h` is used for every `a` ✓; [3] `ha₀ : a₀ < 0` only through L2.3 ✓;
  [2] `g = ratLog` itself satisfies the hypothesis by L2.4 ✓; [5] `map_zsmul` for `→+` ✓.
  SURVIVED.

### Internal node R2 ([6])

`ratLog` is defined through the private `ratCoeff`; L2.1 makes it independent of choices, L2.2
makes it a hom, L2.4–L2.6 are its three properties. A composition failure would need `ratCoeff` to
depend on the witness, excluded by L2.1. SURVIVED.

---

## Result R3 — the real additive valuation of a rank-one valuation (§1.2.1, `RankOne.lean`)

### Plain-English proof (source: [RM] §1.2.1; [Kob84] III §3, III §4)

A rank-one valuation `v` comes with `RankOne.hom v : ValueGroup₀ v →*₀ ℝ≥0`, strictly monotone
(Mathlib). Compose with `NNReal.toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰` (`0 ↦ 0`, `x ↦ exp (log x)`, strictly
monotone by `Real.log_lt_log`) to get `realValuation v : Valuation R ℝᵐ⁰ := v.restrict.map (…)`, and
set `RankOne.addVal v := (realValuation v).addVal`. By `addVal_apply` its value at `x` is `negLog
(toRealMultZero (hom (v.restrict x)))`; when `v x ≠ 0` the hom value is a nonzero real `r`, so this is
`negLog (exp (log r)) = -log r`, the classical `ord x = -log |x|` of [Kob84]; when `v x = 0` the hom
value is `0` and `negLog 0 = ⊤`. Since `addVal v` only depends on the function `hom ∘ restrict`, two
rank-one valuations with the same real absolute value have the same `addVal`. [SRC] `RankOne.lean`
proves all of it over a ring.

### Shared quotes

> **Q3.1** [RM] §1.2.1: "For `v : Valuation R Γ₀` with `[v.RankOne]`, define
> `Valuation.RankOne.realValuation v`, the `ℝᵐ⁰`-valued valuation obtained by pushing `v` along
> `RankOne.hom`, and `Valuation.RankOne.addVal v : AddValuation R (WithTop ℝ)` as its `addVal`.
> Prove `RankOne.addVal v x = -log (hom (v x))` for `v x ≠ 0`, that it is `⊤` exactly at `v x = 0`,
> and that it is unchanged when `v` is replaced by an equivalent valuation with the matching
> `hom`."

> **Q3.2** [Kob84] III §3, p. 66 (PDFPAGE 79): "Let K be an extension of ℚ_p of degree n. For
> α ∈ K we define ord_p α = −log_p |α|_p = −log_p |N_{K/ℚ_p}(α)|_p^{1/n} = −(1/n) log_p
> |N_{K/ℚ_p}(α)|_p. This agrees with the earlier definition of ord_p when α ∈ ℚ_p, and clearly has
> the property that ord_p αβ = ord_p α + ord_p β." (The natural logarithm replaces log_p in the
> unnormalised `addVal`; the normalised members are §1.3–§1.4.)

### Leaves

- **L3.1** (leaf, Mathlib) `RankOne.lean · Valuation.RankOne.addVal_apply` — `addVal v x = negLog
  (toRealMultZero (hom v (v.restrict x)))`. Source Q3.1 ("as its `addVal`"). D: `rfl`
  (`Valuation.map` applies the hom pointwise, definitionally). [SRC] `RankOne.addVal_apply`.
  Attacks: [5] `rfl` compiles in [SRC] with the same definitions ✓; [2] n/a; [4] exact
  unfolding of the clause ✓. SURVIVED.
- **L3.2** (leaf, Mathlib) `RankOne.lean · Valuation.RankOne.addVal_zero` — `addVal v 0 = ⊤`. D:
  `AddValuation.map_zero _`. Attacks: [5] ✓ elaborates; [2] n/a; [4] "`⊤` exactly at `v x = 0`"
  includes `x = 0` ✓. SURVIVED.
- **L3.3** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_eq_top` — `↔ v x = 0`. Source
  Q3.1. D: `rw [addVal, Valuation.addVal_eq_top]`; `show toRealMultZero (hom v (v.restrict x)) = 0 ↔
  v x = 0`; `rw [map_eq_zero, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]` ([SRC]).
  Attacks: [2] `x = 0` ✓; `v x = 1`: hom value `1`, `toRealMultZero 1 = exp 0 ≠ 0` ✓;
  [5] `map_eq_zero` needs `toRealMultZero` injective-at-zero: it is a `→*₀` with
  `toRealMultZero x = 0 ↔ x = 0` (by `if_neg` and `exp_ne_zero`) — [SRC] uses exactly this chain ✓;
  [3] none. SURVIVED.
- **L3.4** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_apply_of_val_ne_zero` — `addVal
  v x = ↑(-Real.log (hom v (v.restrict x)))`. Source Q3.1 ("`-log (hom (v x))` for `v x ≠ 0`"), Q3.2.
  D: `hom v (v.restrict x) ≠ 0` by `hom_eq_zero_iff`, `restrict_eq_zero_iff`; `rw [addVal_apply,
  toRealMultZero_of_ne_zero h, negLog_exp]` ([SRC]).
  Attacks: [3] `hx : v x ≠ 0` necessary (else LHS `⊤`, RHS a real) ✓; [2] `v x = 1`: `-log 1 = 0`
  consistent with `AddValuation.map_one` ✓; [5] L1.2, `NNReal.toRealMultZero_of_ne_zero` ✓.
  SURVIVED.
- **L3.5** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_eq_of_hom_eq` — equal
  `hom ∘ restrict` ⇒ equal `addVal`. Source Q3.1 ("unchanged when `v` is replaced by an equivalent
  valuation with the matching `hom`"; deviation D5 of `plan.md`: equivalence plus matching `hom` is
  exactly the hypothesis). D: `AddValuation.ext fun x ↦ by rw [addVal_apply, addVal_apply, h x]`.
  Attacks: [2] `w = v`: trivial ✓; [3] the hypothesis quantifies over all `x`; a weaker "equal on
  generators" would not suffice for a general ring ✓; [4] the roadmap's hypothesis ("equivalent …
  matching hom") *implies* ours and is what any user has ✓; [5] L3.1 ✓. SURVIVED.

### Internal node R3 ([6])

`addVal v` is the composite `addVal ∘ map (toRealMultZero ∘ hom) ∘ restrict`; L3.1 is its
unfolding and L3.3–L3.5 are consequences of L1.3, L1.2 and the hom's zero behaviour. No
composition gap. SURVIVED.

---

## Result R4 — rational rank one normalised at an element (§1.4, `Commensurable.lean`)

### Plain-English proof (source: [RM] §1.4.1–§1.4.5; [Gou20] 6.4.1–6.4.2, 3.1.3; [Kob84] III §3)

`IsCommensurable v π` says `0 < v π < 1` and every nonzero value is commensurable with `v π`:
`v x ^ n = v π ^ m`, `n > 0` (the density analogue of "the value group is infinite cyclic":
[Gou20] 6.4.2 shows the image of `v_p` on a finite extension is `(1/e)ℤ`; for `ℂ_p` it is `ℚ`,
6.8.7). It implies nontriviality (`π` has `v π ≠ 0, 1`). Let `g₀ := v π` as an element of the
value group `G := valueGroup v ⊂ Γ₀ˣ` (`commGen`); additively `g₀ < 0`. Every `g ∈ G` is
commensurable with `g₀`: by `mem_valueGroup_iff_of_comm`, `g = v x / v a` with `v a ≠ 0`, and
from witnesses `v x ^ n₁ = v π ^ m₁`, `v a ^ n₂ = v π ^ m₂` we get `g ^ (n₁ n₂) = v π ^ (m₁ n₂ −
m₂ n₁)`. So R2 applies to `(Additive G, g₀)`: `ratLog v π := AddCommGroup.ratLog` is the unique
additive hom to `ℚ` with `g₀ ↦ −1`, strictly monotone. Define `addValQ v π := addValValueGroup
v` pushed along `ratLog` (through `WithTop.map`). **Workhorse**: if `v x ^ n = v π ^ m` with
`n > 0`, then in `G`, `n • g = m • g₀` for `g = v x`, so `ratLog g = −m/n` (L2.3) and
`addValQ x = WithTop.map ratLog (negLog g) = −(−m/n) = m/n`. Hence `addValQ π = 1` (witness `1,1`),
`addValQ x ≠ ⊤` for `v x ≠ 0`, and the order reversal `addValQ x ≤ addValQ y ↔ v y ≤ v x`.
**Uniqueness** (§1.4.4): let `w : AddValuation R (WithTop ℚ)` induce the same order and have
`w π = 1`. If `v x = 0` then `w 0 ≤ w x` (from `v x ≤ v 0`) forces `w x = ⊤ = addValQ x`. If
`v x ≠ 0`, take the witness and compare the ring elements `x ^ n · π ^ m⁻` and `π ^ m⁺` (with
`m = m⁺ − m⁻`, `m⁺, m⁻ ∈ ℕ`): their `v`-values agree, so by the order hypothesis their
`w`-values agree: `n • w x + m⁻ • 1 = m⁺ • 1`, and `w x ≠ ⊤` (same argument as the `⊤` case),
so `w x = (m⁺ − m⁻)/n = m/n = addValQ x`. **Rank one**: for `1 < e`, `hom := toNNReal e ∘
mapAddHom' (Rat.cast ∘ ratLog)` is a strictly monotone `→*₀ ℝ≥0` with `hom (v π) = e ^ (ratLog g₀)
= e ^ (−1) = e⁻¹`. **Compatibility `ℚ → ℝ`**: with any rank-one structure, from `v x ^ n = v π ^ m`
apply `hom` and take logs: `n log |x| = m log |π|`, so `−log |x| = (m/n)(−log |π|)`, i.e.
`RankOne.addVal v x = WithTop.map (q ↦ q · (−log |π|)) (addValQ x)`, and exponentiating, `|x| =
|π| ^ (m/n)` — [Gou20] 3.1.3 (iv) with the exponent pinned by `π`.

### Shared quotes

> **Q4.1** [RM] §1.4.1: "Define the Prop class `Valuation.IsCommensurable v π`: `0 < v π`,
> `v π < 1`, and for every `x` with `v x ≠ 0` there are integers `m` and `n > 0` with
> `v x ^ n = v π ^ m`. Prove it implies `v.IsNontrivial`, and that `IsRankOneDiscrete` implies
> `IsCommensurable` at every uniformiser."

> **Q4.2** [RM] §1.4.2 (continuation of Q2.1): "Define `Valuation.addValQ v π : AddValuation R
> (WithTop ℚ)` by pushing the tautological `addValValueGroup` along it, and prove
> `addValQ v π π = 1`."

> **Q4.3** [RM] §1.4.3: "**The workhorse.** `v x ^ n = v π ^ m` with `n > 0` implies
> `addValQ v π x = m / n`. Everything else in this section reduces to it."

> **Q4.4** [RM] §1.4.4: "**Uniqueness.** Any additive valuation `w : AddValuation R (WithTop ℚ)`
> inducing the same order on values as `v` (`w x ≤ w y ↔ v y ≤ v x`) and satisfying `w π = 1`
> equals `addValQ v π`. This is the statement that justifies convention 3: the element pins the
> valuation."

> **Q4.5** [RM] §1.4.5: "**From rational rank one to rank one.** For every real `e > 1`, build
> `RankOne v` with `hom v (v π) = e⁻¹`, and prove the compatibility squares: `RankOne.addVal v` is
> `(-log (hom v (v π)))` times `addValQ v π`, and on a discrete valuation `addValQ v π` is
> `addValZ v` composed with `Int.cast` at a uniformiser `π`."

> **Q4.6** [Gou20] Def. 6.4.1, p. 192 (PDFPAGE 195): "For any x ∈ K, x ≠ 0, we define the p-adic
> valuation v_p(x) to be the unique rational number satisfying |x| = p^{−v_p(x)}. We extend the
> definition formally by setting v_p(0) = +∞." Prop. 6.4.2, p. 193: "The p-adic valuation v_p is
> a homomorphism from the multiplicative group K× to the additive group ℚ. Its image is of the
> form (1/e)ℤ, where e is a divisor of n = [K : ℚ_p]."

> **Q4.7** [Gou20] p. 56 (PDFPAGE 61): "an absolute value defined by |x| = c^{−v_p(x)}, where
> c > 1 was a real number. Now we can check that this is equivalent to the p-adic absolute
> value—just choose α so that c^α = p." (Q2.3 is the equivalence criterion it cites.)

### Leaves

- **L4.1** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.val_ne_zero` — `v π ≠ 0`.
  D: `hπ.val_pos.ne'`. Attacks: [5] ✓; [2]/[3] n/a (a field projection). SURVIVED.
- **L4.2** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.of_forall_eq` —
  transfer along pointwise-equal valuations. New (needed at the `ℂ_p` seam, L10.5). D:
  `constructor <;> simp only [h]`, closing with `hπ.val_pos`, `hπ.val_lt_one`, `hπ.exists_zpow_eq`.
  Attacks: [2] `w = v` ✓; [3] pointwise equality is the weakest hypothesis that transports a
  statement about values ✓; [5] field access ✓. SURVIVED.
- **L4.3** (leaf, Mathlib) `Commensurable.lean · Valuation.IsCommensurable.isNontrivial`. Source
  Q4.1 ("Prove it implies `v.IsNontrivial`"). D: `⟨⟨π, hπ.val_pos.ne', hπ.val_lt_one.ne⟩⟩`
  (`Valuation.IsNontrivial.exists_val_nontrivial : ∃ x, v x ≠ 0 ∧ v x ≠ 1`).
  Attacks: [2] trivial valuation: has no `π` with `0 < v π < 1`, so the class is empty ✓;
  [5] structure shape checked (`names_pre.lean`) ✓; [4] exact clause ✓. SURVIVED.
- **L4.4** (leaf, Mathlib) `Commensurable.lean · Valuation.coe_commGen` — `↑↑(commGen v π) = v π`.
  D: `rfl`. Attacks: [5] `Units.val_mk0` is `rfl` ✓; [2] n/a. SURVIVED.
- **L4.5** (leaf, project) `Commensurable.lean · Valuation.ofMul_commGen_neg` — `ofMul (commGen) < 0`.
  D: `show commGen v π < 1`; `rw [← Subtype.coe_lt_coe, ← Units.val_lt_val]`; `simpa using
  hπ.val_lt_one` ([SRC]). Attacks: [4] sign: `v π < 1` multiplicatively is `< 0` additively ✓
  (this is what makes `ratLog g₀ = −1` and `addValQ π = +1`); [5] `Units.val_lt_val`,
  `Subtype.coe_lt_coe` ✓; [2] n/a. SURVIVED.
- **L4.6** (leaf, Mathlib) `Commensurable.lean · Valuation.isCommensurableWith_commGen` — every
  `g ∈ valueGroup v` is commensurable with `commGen`. Source Q4.1 (every *value*) + the closure
  argument of the prose ([Gou20] 6.4.2: "Its image is therefore an additive subgroup"). D: [SRC]
  `exists_zpow_eq_commGen`: `mem_valueGroup_iff_of_comm` gives `a, x` with `v a ≠ 0`, `v a * g =
  v x`; witnesses `(m₁ n₂ − m₂ n₁, n₁ n₂)`; `Subtype.ext`, `Units.ext`, `div_zpow`, `zpow_sub₀`,
  `zpow_mul`.
  Attacks: [1] a value group element not of the form `v x / v a` would break this — Mathlib's
  `valueGroup` is the subgroup generated by the values, and `mem_valueGroup_iff_of_comm` says
  exactly that every element is such a quotient ✓; [2] `g = 1`: witnesses `(0, 1)` ✓; `g = commGen`:
  `(1,1)` ✓; [5] four Mathlib names elaborate ✓. SURVIVED.
- **L4.7** (leaf, project) `Commensurable.lean · Valuation.ratLog_strictMono`. D:
  `AddCommGroup.ratLog_strictMono _ _` (L2.5). Attacks: [5] ✓; [4] Q2.1 ✓. SURVIVED.
- **L4.8** (leaf, project) `Commensurable.lean · Valuation.ratLog_commGen` — `= −1`. D:
  `AddCommGroup.ratLog_self _ _` (L2.4). Attacks: [5] ✓. SURVIVED.
- **L4.9** (leaf, project) `Commensurable.lean · Valuation.ratLog_eq_of_zsmul`. D:
  `AddCommGroup.ratLog_eq _ _ hn hmn` (L2.3). Attacks: [5] ✓. SURVIVED.
- **L4.10** (leaf, Mathlib) `Commensurable.lean · Valuation.addValQ_apply` — `= WithTop.map (ratLog)
  (addValValueGroup x)`. D: `rfl` (`AddValuation.map_apply`, `AddMonoidHom.withTopMap` coerces to
  `WithTop.map`). Attacks: [5] [SRC] `addValQ_apply` is `rfl` ✓. SURVIVED.
- **L4.11** (leaf, Mathlib) `Commensurable.lean · Valuation.addValQ_zero`. D: `AddValuation.map_zero
  _`. SURVIVED ([5] ✓).
- **L4.12** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_top` — `↔ v x = 0`. D:
  `rw [addValQ_apply, WithTop.map_eq_top_iff, addValValueGroup_eq_top]` (L1.20).
  Attacks: [5] `WithTop.map_eq_top_iff` (Mathlib, `Order/WithBot.lean`) — verified in the ticket
  name check; [2] `x = 0` ✓. SURVIVED.
- **L4.13** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_of_zpow` — **the workhorse**.
  Source Q4.3. D ([SRC] `addValQ_eq_of_zpow`): `g := WithZero.unzero (v.restrict x ≠ 0)`; `n •
  ofMul g = m • ofMul (commGen)` from `hmn` via `Subtype.ext`, `Units.ext`,
  `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `coe_commGen`, `embedding_restrict`;
  then `rw [addValQ_apply, addValValueGroup_of_coe, WithTop.map_coe, map_neg, ratLog_eq_of_zsmul,
  neg_neg]`.
  Attacks: [1] two witnesses give the same value by L2.1 ✓; [2] `x = π`, `(m, n) = (1, 1)`: `1`
  ✓; `m = 0`: `v x ^ n = 1` ⇒ `v x = 1` ⇒ `addValQ x = 0` ✓; `m < 0`: value negative — `zpow`
  handles negative `m` ✓; [3] `hx` is needed to form `g` (else LHS `⊤`); `hn : 0 < n` is needed
  (for `n = 0` the hypothesis is vacuous) ✓; [5] all names elaborate ✓. SURVIVED.
- **L4.14** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_of_pow_eq_pow` — natural
  exponents. D: L4.13 with `(m : ℤ) (n : ℤ)` after `zpow_natCast` on both sides; casts by
  `Int.cast_natCast`; `Nat.cast_pos.mpr hn`.
  Attacks: [2] `n = 1` ✓; [5] `zpow_natCast`, `Int.cast_natCast` ✓. SURVIVED.
- **L4.15** (leaf, project) `Commensurable.lean · Valuation.addValQ_self` — `addValQ v π π = 1`.
  Source Q4.2. D: `addValQ_eq_of_zpow v π (val_ne_zero) one_pos rfl` then `norm_num`.
  Attacks: [4] the roadmap's normalisation `addValQ v π π = 1` — sign chain checked:
  `negLog (exp g₀) = −g₀`, `ratLog (−g₀) = −ratLog g₀ = 1` ✓; [5] L4.13 ✓. SURVIVED.
- **L4.16** (leaf, project) `Commensurable.lean · Valuation.addValQ_ne_top`. D: witnesses from
  `hπ.exists_zpow_eq`, L4.13, `WithTop.coe_ne_top`. Attacks: [2] ✓; [5] ✓. SURVIVED.
- **L4.17** (leaf, project) `Commensurable.lean · Valuation.exists_zpow_eq_and_addValQ`
  (shared-witness existential). D: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; exact ⟨m, n, hn,
  e, addValQ_eq_of_zpow v π hx hn e⟩`. Attacks: [5] ✓; shape justified in the gate-7 check.
  SURVIVED.
- **L4.18** (leaf, project) `Commensurable.lean · Valuation.addValQ_le_addValQ` — order reversal.
  New API (used by L6.8 and in the uniqueness argument's `⊤` case). D: `rw [addValQ_apply,
  addValQ_apply, WithTop.map_le_iff _ (ratLog_strictMono v π).le_iff_le, addValValueGroup_apply,
  addValValueGroup_apply, negLog_le_negLog, Valuation.restrict_le_iff]`.
  Attacks: [2] `y = 0`: `_ ≤ ⊤ ↔ 0 ≤ v x` ✓; [5] `WithTop.map_le_iff` (Mathlib, statement `map f
  a ≤ map f b ↔ a ≤ b` given `∀ a b, f a ≤ f b ↔ a ≤ b`) — verified in the ticket name check;
  `restrict_le_iff` ✓. SURVIVED.
- **L4.19** (leaf, project) `Commensurable.lean · Valuation.addValQ_unique` — **M2**. Source Q4.4.
  D: `AddValuation.ext fun x ↦ ?_`. Case `v x = 0`: `hw 0 x` with `v x ≤ v 0 = 0` gives `w 0 ≤ w x`,
  `w 0 = ⊤` (`AddValuation.map_zero`), so `w x = ⊤` (`top_le_iff`); RHS `⊤` by L4.12. Case `v x ≠ 0`:
  `⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx`; set `a := m.toNat`, `b := (-m).toNat`, so `(a : ℤ) − b
  = m` (`Int.toNat_sub_toNat_neg`); the ring elements `x ^ n.toNat * π ^ b` and `π ^ a` have equal
  `v`-values (`map_mul, map_pow`, `zpow_natCast`, `e`, `← zpow_add₀ (val_ne_zero)`); apply `hw`
  both ways to get `w (x ^ n.toNat * π ^ b) = w (π ^ a)`, i.e. `n • w x + b • 1 = a • 1`
  (`AddValuation.map_mul, map_pow`, `hwπ`); `w x ≠ ⊤` (as in the first case, with `v 0 ≤ v x` false
  direction: if `w x = ⊤` then `w 0 ≤ w x`, so `v x ≤ v 0 = 0`, contradiction); write `w x = ↑q`,
  solve `n q + b = a` in `ℚ` (`WithTop.coe_inj`, `nsmul_eq_mul`, `field_simp`, `linarith`/`ring`) to
  get `q = m / n`; conclude with L4.13.
  Attacks: [1] without `w π = 1`, `w = 2 • addValQ` satisfies the order hypothesis — so `hwπ` is
  necessary ✓; without commensurability, two independent values leave `w` undetermined — the
  class is used through the witness ✓; [2] `w := addValQ v π` satisfies both hypotheses (L4.18,
  L4.15) so the statement is consistent ✓; `x = 0`: handled by the first case ✓; `x = π`: `w π = 1
  = addValQ π` ✓; [3] the order hypothesis is an `↔` for all pairs; the proof uses it in both
  directions (equal values ⇒ equal `w`-values, and the `⊤` case) — a one-directional hypothesis
  would not suffice ✓; [4] Q4.4 verbatim ✓; [5] `Int.toNat_sub_toNat_neg`, `zpow_add₀`,
  `AddValuation.map_pow`, `top_le_iff` — verified in the ticket name check. SURVIVED.
- **L4.20** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.toRankLeOne`
  (`strictMono'`). Source Q4.5. D: `(WithZeroMulReal.toNNReal_strictMono he).comp
  (mapAddHom'_strictMono (Rat.cast_strictMono.comp (ratLog_strictMono v π)))` ([SRC], with
  `Rat.cast_strictMono : StrictMono ((↑) : ℚ → ℝ)`).
  Attacks: [3] `1 < e` is needed for strict monotonicity of `e ^ ·` (for `e = 1` the hom is
  constant, for `e < 1` decreasing) ✓; [5] names ✓ (L1.12, R1's `toNNReal_strictMono`). SURVIVED.
- **L4.21** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.toRankOne_hom_restrict`
  — `hom v (v.restrict π) = e⁻¹`. Source Q4.5 ("with `hom v (v π) = e⁻¹`"). D: `v.restrict π = exp
  (ofMul (commGen v π))` as elements of `(Additive G)ᵐ⁰` (by `ValueGroup₀.embedding_injective`,
  `embedding_restrict`, `coe_commGen`); then `mapAddHom'_exp`, `ratLog_commGen`, `Rat.cast_neg,
  Rat.cast_one`, `toNNReal_exp`, `NNReal.rpow_neg_one`.
  Attacks: [2] `e = 2`: `2 ^ (−1) = 1/2` ✓; [4] Q4.5 ✓; [5] `NNReal.rpow_neg_one` — verified in the
  ticket name check; the `letI` statement elaborates (signature line 143–145) ✓. SURVIVED.
- **L4.22** (leaf, project) `Commensurable.lean · Valuation.RankOne.addVal_eq_map_addValQ` — the
  square `ℚ → ℝ`. Source Q4.5, Q4.7. D ([SRC]): case `v x = 0` (both `⊤`); else
  `exists_zpow_eq_and_addValQ`, `hres : v.restrict x ^ n = v.restrict π ^ m` by embedding
  injectivity, apply `hom` (`map_zpow₀`), coerce to `ℝ`, `Real.log_zpow` twice, then
  `RankOne.addVal_apply_of_val_ne_zero`, `WithTop.map_coe`, `WithTop.coe_inj`, `push_cast`,
  `field_simp`, `linarith`.
  Attacks: [2] `x = π`: `addVal π = −log |π| = 1 · (−log |π|)` ✓; [3] `[RankOne v]` is any rank-one
  structure, not necessarily `toRankOne` — the statement is about *its* hom, correct for all ✓;
  [5] `Real.log_zpow` ✓. SURVIVED.
- **L4.23** (leaf, project) `Commensurable.lean · Valuation.RankOne.hom_eq_rpow_addValQ` —
  `|x| = |π| ^ q`. Source Q4.7 ([Gou20] 3.1.3 (iv) with pinned exponent), Q4.5. D ([SRC]): from
  L4.22 at `x`, `Real.rpow_def_of_pos`, `Real.exp_log`, `linarith`.
  Attacks: [3] `hq` carries `v x ≠ 0` implicitly (a `⊤` value is not a `↑q`) — the proof recovers
  `hx` from it ✓; [2] `q = 1`, `x = π` ✓; `q = 0`: `|x| = 1` ✓; [5] names ✓. SURVIVED.

### Internal node R4 ([6])

The children could all hold while `addValQ` were not an additive valuation only if
`AddValuation.map` were misapplied; it is Mathlib's, and the monotonicity argument is L4.7. The
uniqueness L4.19 is stated against `addValQ` itself, so a wrong normalisation sign would have
surfaced in L4.15. SURVIVED.

---

## Result R5 — discrete rank one: the `ℤ`-valued additive valuation (§1.3.1–§1.3.3, `Discrete.lean`)

### Plain-English proof (source: [RM] §1.3.1–§1.3.3; [Kob84] III §3; [Gou20] 6.4.4–6.4.5)

For `[v.IsRankOneDiscrete]` Mathlib provides `generator v : Γ₀ˣ` with `generator < 1` and `zpowers
(generator) = valueGroup v`, and an order isomorphism `valueGroup₀_equiv_withZeroMulInt v :
ValueGroup₀ v ≃*o ℤᵐ⁰` with `generator' ^ k ↦ exp (−k)`. Every nonzero value is `generator ^ k`
(membership in `zpowers`), and for a uniformiser `π` (an element with `v π = generator`) this reads
`v x = v π ^ k` — [Kob84]'s "`x = π^m u`" with `m = e·ord_p x` and [Gou20] 6.4.5 (ii). Hence a
discrete valuation is commensurable at any element with `0 < v π < 1` (`v π = g^j` with `j ≥ 1`,
`v x = g^k`, so `(v x)^j = (v π)^k`), in particular at every uniformiser. Define `addValZ v :=
(v.restrict.map equiv).addVal`; its value is `negLog (equiv (v.restrict x))`, `⊤` iff `v x = 0`,
and `addValZ x = k ↔ v x = generator ^ k` (through `negLog_eq_coe`, `equiv (generator'^k) =
exp (−k)` and injectivity), so `addValZ x = k ↔ v x = v π ^ k` at a uniformiser and `addValZ π = 1`.
Compatibility with the `ℚ`-valued valuation at a uniformiser: `v x = v π ^ k` gives `addValQ x =
k/1 = k` by the workhorse. **Norm recovery**: a `→*₀` out of `ValueGroup₀ v ≅ ℤᵐ⁰` is determined by
its value on the generator (every unit is `generator'^k`), so if `hom (generator') = e⁻¹` then
`hom = toNNReal e ∘ equiv`, whence `hom (v x) = toNNReal e (exp (−d)) = e^(−d)` when `addValZ x = d`
— the `ℚ_p` model `|x|_p = p^{−ord_p x}` of [Kob84] I §2.

### Shared quotes

> **Q5.1** [RM] §1.3.1: "Define `Valuation.IsRankOneDiscrete.addValZ v : AddValuation R (WithTop ℤ)`
> and prove its characterisation: `addValZ v x = k ↔ v x = generator v ^ k`, with `⊤` exactly at
> `v x = 0`."

> **Q5.2** [RM] §1.3.2: "Prove `addValZ v π = 1` for every uniformiser `π`, and `addValZ v x = k ↔
> v x = v π ^ k` for such a `π`."

> **Q5.3** [RM] §1.3.3: "**Norm recovery.** If `[v.RankOne]` as well and `hom v (generator v) = e⁻¹`
> for a real `e > 1`, then `hom v (v x) = e ^ (-(addValZ v x))` for `v x ≠ 0`. Prove that on a
> discrete valuation the single scalar `e` determines `hom`, because a monoid-with-zero hom out of
> an infinite cyclic group is determined by its value on the generator."

> **Q5.4** [Kob84] III §3, p. 66 (PDFPAGE 79): "Now let π ∈ K be any element such that ord_p π =
> (1/e). Then clearly any x ∈ K can be written uniquely in the form π^m u, where |u|_p = 1 and
> m ∈ ℤ (in fact, m = e·ord_p x)."

> **Q5.5** [Gou20] Def. 6.4.4, p. 194 and Prop. 6.4.5 (ii), p. 195 (PDFPAGE 197–198): "We say an
> element π ∈ K is a uniformizer if v_p(π) = 1/e." — "Any element x ∈ K can be written in the form
> x = uπ^{e v_p(x)}, where u ∈ O_K^× is a unit, and therefore satisfies v_p(u) = 0."

> **Q5.6** [Kob84] I §2, p. 2 (PDFPAGE 15): "For any nonzero integer a, let ord_p a be the highest
> power of p which divides a … (If a = 0, we agree to write ord_p 0 = ∞.) Note that ord_p behaves a
> little like a logarithm would: ord_p(a₁a₂) = ord_p a₁ + ord_p a₂." and (the display, OCR
> normalised) "|x|_p = p^{−ord_p x} if x ≠ 0; 0 if x = 0."

> **Q5.7** [Mathlib] `Valuation.IsRankOneDiscrete` docstring: "a valuation `v : A → Γ` on a ring `A`
> is *discrete*, if `genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
> asking that `1 : ℤ` belongs to the image of the corresponding additive valuation."

### Leaves

- **L5.1** (leaf, Mathlib) `Discrete.lean · Valuation.IsRankOneDiscrete.exists_zpow_generator_eq`.
  Source Q5.1 (the generator), Q5.4. D: `Units.mk0 (v x) hx ∈ valueGroup` (`mem_valueGroup _ ⟨x,
  rfl⟩`); `rw [← generator_zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at this`; `⟨k, by rw
  [← Units.val_mk0 hx, ← hk]⟩`.
  Attacks: [2] `v x = 1`: `k = 0` ✓; [3] `hx` necessary (`0` is not a unit power) ✓; [5] names ✓.
  SURVIVED.
- **L5.2** (leaf, Mathlib) `Discrete.lean · …exists_zpow_eq_of_isUniformizer`. Source Q5.4, Q5.5.
  D ([SRC]): `hπ.zpowers_eq_valueGroup`, `Subgroup.mem_zpowers_iff`, `Units.val_zpow_eq_zpow_val`,
  `Units.val_mk0`. Attacks: as L5.1 ✓; [4] "`x = π^m u`" ⇒ `v x = v π ^ m` ✓. SURVIVED.
- **L5.3** (leaf, project) `Discrete.lean · …isCommensurable_of_lt_one` — commensurable at any
  `0 < v π < 1`. New (generalises Q4.1's "at every uniformiser"; needed for L9.5). D: `val_pos :=
  zero_lt_iff.mpr h0`; `exists_zpow_eq x hx`: L5.1 for `x` (`k`) and for `π` (`j`); `0 < j` from
  `generator ^ j < 1` and `generator < 1` (`zpow_lt_one_iff_right_of_lt_one₀` on `Γ₀ˣ`/`Γ₀`, or
  `Units.val_lt_val` and `zpow_lt_one_iff_right_of_lt_one₀`); witnesses `(k, j)`: `(g^k)^j = g^{kj}
  = (g^j)^k` (`← zpow_mul, mul_comm, zpow_mul`).
  Attacks: [1] for `v π = 1` the conclusion is false (`val_lt_one`) — excluded by `h1` ✓; [2]
  `π` a uniformiser: `j = 1` ✓; `v π = g^2`: `v x = g` has witnesses `(1, 2)` ✓; [3] `h0, h1` are
  exactly the class's first two fields, so nothing weaker can do ✓; [5] `zpow_lt_one_iff_right_of_lt_one₀`
  — verified in the ticket name check. SURVIVED.
- **L5.4** (leaf, project) `Discrete.lean · …isCommensurable` — at a uniformiser. Source Q4.1
  ("`IsRankOneDiscrete` implies `IsCommensurable` at every uniformiser"). D: `isCommensurable_of_lt_one
  v hπ.val_ne_zero hπ.val_lt_one` (or [SRC] directly with `(k, 1)`). Attacks: [5] ✓; [2] ✓. SURVIVED.
- **L5.5** (leaf, Mathlib) `Discrete.lean · …addValZ_apply`. D: `rfl`. SURVIVED ([5] [SRC] `rfl`).
- **L5.6** (leaf, Mathlib) `Discrete.lean · …addValZ_zero`. D: `AddValuation.map_zero _`. SURVIVED.
- **L5.7** (leaf, project) `Discrete.lean · …addValZ_eq_top` — `↔ v x = 0`. Source Q5.1 ("with `⊤`
  exactly at `v x = 0`"). D: `rw [addValZ_apply, negLog_eq_top, map_eq_zero, restrict_eq_zero_iff]`
  (`map_eq_zero` for the `≃*o` coerced to `→*₀`: `MonoidWithZeroHom.coe_ofClass`).
  Attacks: [2] `x = 0` ✓; [5] `map_eq_zero` needs the equivalence as a `MonoidWithZeroHomClass`
  map — `MulEquivClass` gives it (Mathlib `MulEquivClass.toMonoidWithZeroHomClass`) ✓. SURVIVED.
- **L5.8** (leaf, project) `Discrete.lean · …addValZ_eq_iff` — `addValZ x = k ↔ v x = ↑(generator ^ k)`.
  Source Q5.1. D: `rw [addValZ_apply, negLog_eq_coe]`; `v.restrict x = generator' ^ k ↔ equiv (…) =
  exp (−k)` by `(equiv).injective.eq_iff` and `valueGroup₀_equiv_withZeroMulInt_apply_zpow`; then
  `embedding_injective.eq_iff`, `map_zpow₀`, `embedding_generator'`, `embedding_restrict`,
  `Units.val_zpow_eq_zpow_val`.
  Attacks: [2] `k = 0`: `addValZ x = 0 ↔ v x = 1` ✓; `k = 1`: `↔ v x = generator` = `IsUniformizer`
  ✓ (consistent with L5.11); [4] Q5.1 verbatim; the roadmap writes `generator v ^ k` in `Γ₀`,
  the skeleton coerces from `Γ₀ˣ` — same element ✓; [5] `valueGroup₀_equiv_withZeroMulInt_apply_zpow
  : equiv (generator' ^ k) = exp (−k)` elaborates with exactly this shape ✓. SURVIVED.
- **L5.9** (leaf, project) `Discrete.lean · …addValZ_eq_of_zpow`. Source Q5.2. D ([SRC]): `h1 :
  v.restrict x = v.restrict π ^ k` (embedding injectivity), `h2 : v.restrict π = generator'`
  (embedding, `hπ`), `rw [h1, h2, valueGroup₀_equiv_withZeroMulInt_apply_zpow]`, `negLog_eq_coe`.
  Attacks: [2] `k = 1`, `x = π` ✓; [5] ✓. SURVIVED.
- **L5.10** (leaf, project) `Discrete.lean · …addValZ_eq_iff_of_isUniformizer`. Source Q5.2. D:
  L5.8 with `hπ : v π = ↑generator` (`IsUniformizer.val`) and `Units.val_zpow_eq_zpow_val`.
  Attacks: [2] as L5.8 ✓; [5] ✓. SURVIVED.
- **L5.11** (leaf, project) `Discrete.lean · …addValZ_isUniformizer` — `addValZ π = 1`. Source
  Q5.2, Q5.7 ("`1 : ℤ` belongs to the image"). D: `addValZ_eq_of_zpow v hπ (zpow_one _).symm`
  (`k = 1`), `WithTop.coe_one`. Attacks: [4] Q5.2 verbatim ✓; [5] ✓. SURVIVED.
- **L5.12** (leaf, project) `Discrete.lean · …addValZ_le_addValZ`. New API. D: `rw [addValZ_apply,
  addValZ_apply, negLog_le_negLog, (valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le,
  restrict_le_iff]`. Attacks: [2] `y = 0` ✓; [5] ✓. SURVIVED.
- **L5.13** (leaf, project) `Discrete.lean · Valuation.addValQ_eq_map_addValZ`. Source Q4.5 ("on a
  discrete valuation `addValQ v π` is `addValZ v` composed with `Int.cast` at a uniformiser `π`").
  D ([SRC]): case `v x = 0` (both `⊤`); else `k` from L5.2, `addValQ_eq_of_zpow v π hx one_pos (by
  rw [zpow_one, hk])`, `addValZ_eq_of_zpow v hπ hk`, `WithTop.map_coe`, `norm_num`.
  Attacks: [2] `x = π`: `1 = ↑1` ✓; [3] the `IsCommensurable` instance is a hypothesis although
  derivable (L5.4): keeping it an instance argument lets the statement be used with *any*
  instance — all instances of a `Prop` class are equal ✓; [5] ✓. SURVIVED.
- **L5.14** (leaf, project) `Discrete.lean · …hom_eq_toNNReal_comp` — `hom` determined by its value
  on `generator'`. Source Q5.3 ("a monoid-with-zero hom out of an infinite cyclic group is determined
  by its value on the generator"). D ([SRC] `hb_of_norm_generator`): `MonoidWithZeroHom.ext`;
  `induction γ using WithZero.recZeroCoe` (zero: `simp`; coe `u`: `u = generator' ^ k` by
  `generator'_zpowers_eq_top`, `Subgroup.mem_zpowers_iff`), then `MonoidWithZeroHom.comp_apply,
  coe_ofClass, WithZero.coe_zpow, valueGroup₀_equiv_withZeroMulInt_apply_zpow, toNNReal_neg_apply,
  map_zpow₀, hgen, inv_zpow, ← zpow_neg`.
  Attacks: [1] for a non-cyclic value group the statement is false — `IsRankOneDiscrete` is the
  hypothesis ✓; [2] `k = 0`: both sides `1` ✓; [3] `he : e ≠ 0` is what `toNNReal` needs; the
  roadmap's `e > 1` is stronger — we state the weaker hypothesis, true as proved ✓; [5] names ✓
  (`WithZeroMulInt.toNNReal_neg_apply : x ≠ 0 → toNNReal he x = e ^ (unzero hx).toAdd`). SURVIVED.
- **L5.15** (leaf, project) `Discrete.lean · …hom_eq_zpow_neg_addValZ` — `hom (v x) = e ^ (−d)`.
  Source Q5.3, Q5.6. D ([SRC]): `rw [addValZ_apply, negLog_eq_coe] at hd`; `rw [hom_eq_toNNReal_comp
  v he hgen, comp_apply, coe_ofClass, hd, toNNReal_neg_apply]`, `unzero (exp (−d)) = ofAdd (−d)`.
  Attacks: [2] `d = 0`: `1` ✓; `x = π`, `d = 1`: `e⁻¹` ✓ (consistent with `hgen`); [3] `he : e ≠ 0`
  (not `1 < e`) suffices, as in L5.14 ✓; [4] Q5.3 verbatim (the roadmap's `-(addValZ v x)` is our
  `d` with `addValZ x = d`) ✓; [5] ✓. SURVIVED.
- **L5.16** (leaf, project) `Discrete.lean · …hom_eq_zpow_neg_addValZ_of_isUniformizer`. D:
  `v.restrict π = generator'` (embedding injectivity + `hπ`), so `hπe` is `hgen`; apply L5.15.
  Attacks: [5] ✓; [2] as L5.15. SURVIVED.

### Internal node R5 ([6])

`addValZ` is the R1 dictionary applied to `v.restrict.map equiv`; L5.8 is the only place the
isomorphism's formula enters, and everything else is derived from L5.8/L5.9. The norm-recovery
pair L5.14–L5.15 composes `hom = toNNReal ∘ equiv` with `equiv (v.restrict x) = exp (−d)`; a
mismatch of sign conventions (`exp (−k)` vs `exp k`) would have broken L5.8 against Mathlib's
`_apply_zpow`. SURVIVED.

---

## Result R6 — the three valuations of an ultrametric normed field (§1.2.2–§1.2.3, §1.3.4, §1.4.6, `Normed.lean`)

### Plain-English proof (source: [RM] §1.2.2–§1.2.3, §1.3.4, §1.4.6; [Kob84] III §4; [Gou20] 3.1)

For a nontrivially normed ultrametric field `K`, Mathlib's `NormedField.valuation : Valuation K ℝ≥0`
is `‖·‖₊` with a `RankOne` structure whose `hom` is the embedding of the value group, so `v.norm x =
‖x‖` and `‖x‖ = hom (v.restrict x)`. Then `normAddVal K := RankOne.addVal valuation` has value
`−log ‖x‖` at `x ≠ 0` (L3.4 + L6.2), `⊤` at `0`, reverses the order of norms, and is characterised
by `‖x‖ = exp (−r)` where `r` is its value — the only additive valuation into `WithTop ℝ` with
this property, because the property determines the value `r = −log ‖x‖` at every `x ≠ 0` and
`map_zero` fixes `0`. In the discrete case `normAddValZ K := addValZ valuation`: at a uniformiser
`π`, `normAddValZ x = k ↔ ‖x‖ = ‖π‖ ^ k` (L5.10 read through `‖·‖₊`), `normAddValZ π = 1`, and
`‖x‖ = e ^ (−d)` when `‖π‖ = e⁻¹` ([Kob84] I §2 for `ℚ_p`); the real valuation is `(−log ‖π‖)` times
the integer one. In the rational-rank-one case `normAddValQ K π := addValQ valuation π`, with
`normAddValQ π = 1`, the workhorse read off norms, `‖x‖ = ‖π‖ ^ q` (L4.23) — no base, no
factorisation hypothesis — and the two squares `normAddVal = (−log ‖π‖) · normAddValQ` (L4.22) and
`normAddValQ = Int.cast ∘ normAddValZ` (L5.13).

### Shared quotes

> **Q6.1** [RM] §1.2.2: "For an ultrametric normed field, define `NormedField.normAddVal K :
> AddValuation K (WithTop ℝ)` from `NormedField.valuation`, and prove `normAddVal K x = -log ‖x‖`
> for `x ≠ 0`. This is the unnormalised member of the family: it takes no element and
> `normAddVal K π` is `-log ‖π‖`, not `1`."

> **Q6.2** [RM] §1.2.3: "Prove the defining equivalence `‖x‖ = exp (-(normAddVal K x))` for
> `x ≠ 0`, and that `normAddVal K` is the unique additive valuation into `WithTop ℝ` satisfying
> it."

> **Q6.3** [RM] §1.3.4: "For an ultrametric normed field whose valuation is discrete, define
> `NormedField.normAddValZ K : AddValuation K (WithTop ℤ)` and prove
> `‖x‖ = e ^ (-(normAddValZ K x))` when a uniformiser has norm `e⁻¹`."

> **Q6.4** [RM] §1.4.6: "**Norm recovery.** For an ultrametric normed field, define
> `NormedField.normAddValQ K π` and prove `‖x‖ = ‖π‖ ^ (normAddValQ K π x)` for `x ≠ 0`. ⚠ There is
> no exponential base and no factorisation hypothesis in this statement: normalising at `π` pins
> the base to `‖π‖⁻¹`."

> **Q6.5** [Kob84] III §4, p. 72 (PDFPAGE 85): "We also extend ord_p to Ω: ord_p x = −log_p |x|_p."

> **Q6.6** [Mathlib] `NormedField.valuation_apply : valuation x = ‖x‖₊` and the `RankOne` instance
> for `[NontriviallyNormedField K] [IsUltrametricDist K]` with `hom' := ValueGroup₀.embedding`
> (`Mathlib/Topology/Algebra/Valued/NormedValued.lean`).

### Leaves

- **L6.1** (leaf, project) `Normed.lean · Valuation.RankOne.addVal_apply_of_ne_zero` (field) —
  `addVal v x = ↑(−log (v.norm x))`. Source Q3.1/Q6.5. D ([SRC]): `hom v (v.restrict x) ≠ 0` from
  `hom_eq_zero_iff`, `restrict_eq_zero_iff`, `v.zero_iff`; `rw [addVal_apply,
  toRealMultZero_of_ne_zero h, negLog_exp]; rfl` (`Valuation.norm_def`).
  Attacks: [3] a field is needed for `v x ≠ 0 ↔ x ≠ 0` (`Valuation.zero_iff`) ✓; [5] ✓. SURVIVED.
- **L6.2** (leaf, Mathlib) `Normed.lean · NormedField.valuation_norm_eq` — `valuation.norm x = ‖x‖`.
  Source Q6.6. D ([SRC]): `rw [Valuation.norm_def, Valuation.restrict_def]; show
  ((embedding (restrict₀ _ x) : ℝ≥0) : ℝ) = ‖x‖; rw [embedding_restrict₀]; rfl`.
  Attacks: [5] the `RankOne` instance's `hom'` is literally `embedding` (Q6.6), so the `show` is
  definitional ✓; [2] `x = 0`: `0 = 0` ✓. SURVIVED.
- **L6.3** (leaf, project) `Normed.lean · NormedField.norm_eq_coe_hom`. D: `rw [← valuation_norm_eq
  K x]; rfl`. SURVIVED ([5] [SRC]).
- **L6.4** (leaf, Mathlib) `Normed.lean · NormedField.normAddVal_zero`. D: `AddValuation.map_zero _`.
  SURVIVED.
- **L6.5** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_top` — `↔ x = 0`. D:
  `RankOne.addVal_eq_top` (L3.3), `Valuation.zero_iff`. Attacks: [2] ✓; [5] ✓. SURVIVED.
- **L6.6** (leaf, project) `Normed.lean · NormedField.normAddVal_apply_of_ne_zero` — `= ↑(−log ‖x‖)`.
  Source Q6.1. D ([SRC]): `rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]`.
  Attacks: [2] `‖x‖ = 1`: `0` ✓; [4] Q6.1 verbatim ✓; [5] L6.1, L6.2 ✓. SURVIVED.
- **L6.7** (leaf, project) `Normed.lean · NormedField.exists_normAddVal_eq_and_norm_eq_exp_neg`.
  Source Q6.2 ("the defining equivalence"). D: `⟨-Real.log ‖x‖, normAddVal_apply_of_ne_zero K hx,
  by rw [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]⟩`.
  Attacks: [3] `hx` necessary (`‖0‖ = 0` is not an `exp`) ✓; [5] `Real.exp_log`, `norm_pos_iff` ✓.
  SURVIVED.
- **L6.8** (leaf, project) `Normed.lean · NormedField.normAddVal_le_normAddVal` — `↔ ‖y‖ ≤ ‖x‖`. New
  API (convention 6 orientation). D: `normAddVal` unfolds to `(realValuation v).addVal`;
  `addVal_le_addVal` (L1.17); `realValuation v y ≤ realValuation v x ↔ v y ≤ v x` by the strict
  monotonicity of `toRealMultZero ∘ hom` (`StrictMono.le_iff_le`), then `valuation_apply`,
  `NNReal.coe_le_coe`.
  Attacks: [2] `y = 0` ✓; [5] L1.17 and `StrictMono.le_iff_le` ✓. SURVIVED.
- **L6.9** (leaf, project) `Normed.lean · NormedField.normAddVal_unique`. Source Q6.2 ("the unique
  additive valuation"). D: `AddValuation.ext fun x ↦ ?_`; `x = 0`: `AddValuation.map_zero` twice;
  `x ≠ 0`: `⟨r, hr, hx⟩ := hw x hx'`; `r = −log ‖x‖` from `hx` by `Real.log_exp` (apply `Real.log`,
  `neg_neg`); `rw [hr, normAddVal_apply_of_ne_zero K hx']`.
  Attacks: [1] a second valuation with the same property would have the same values — this is the
  proof; the hypothesis is used at every `x ≠ 0` ✓; [2] `w := normAddVal K` satisfies the
  hypothesis by L6.7 ✓; [3] the hypothesis is the defining equivalence of Q6.2 exactly (`∃ r`
  avoids `exp` of a `WithTop ℝ`, deviation noted in `plan.md` design 7) ✓; [5] `Real.log_exp` ✓.
  SURVIVED.
- **L6.10** (leaf, Mathlib) `Normed.lean · NormedField.normAddValZ_zero`. D: `map_zero`. SURVIVED.
- **L6.11** (leaf, project) `Normed.lean · NormedField.normAddValZ_eq_top`. D: L5.7,
  `Valuation.zero_iff`. SURVIVED ([2] ✓, [5] ✓).
- **L6.12** (leaf, project) `Normed.lean · NormedField.normAddValZ_eq_iff_of_isUniformizer` —
  `normAddValZ x = k ↔ ‖x‖ = ‖π‖ ^ k`. Source Q5.2 read through the norm, Q5.4. D: L5.10, then
  `valuation_apply`, `← NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`.
  Attacks: [2] `k = 0`: `‖x‖ = 1` ✓; `x = 0`: both sides false (`⊤ ≠ ↑k`; `0 ≠ ‖π‖^k` as `π ≠ 0`)
  ✓; [5] `NNReal.coe_zpow`, `coe_nnnorm` ✓. SURVIVED.
- **L6.13** (leaf, project) `Normed.lean · NormedField.normAddValZ_isUniformizer`. D: L5.11.
  SURVIVED.
- **L6.14** (leaf, project) `Normed.lean · NormedField.norm_eq_zpow_neg_normAddValZ` — generator
  form. Source Q6.3, Q5.3. D ([SRC]): `rw [norm_eq_coe_hom K x, hom_eq_zpow_neg_addValZ _ he hgen
  hd, NNReal.coe_zpow]`.
  Attacks: [3] `he : e ≠ 0`; the roadmap's `e > 1` is implied by `hgen` and `generator < 1` but
  is not needed ✓; [2] `d = 0` ✓; [5] L5.15 ✓. SURVIVED.
- **L6.15** (leaf, project) `Normed.lean · NormedField.norm_eq_zpow_neg_normAddValZ_of_isUniformizer`
  — `‖π‖ = e⁻¹ → ‖x‖ = e ^ (−d)`. Source Q6.3 verbatim ("when a uniformiser has norm `e⁻¹`"), Q5.6.
  D: `(normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd`, `hπe`, `inv_zpow'`/`inv_zpow`,
  `zpow_neg`.
  Attacks: [2] `K = ℚ_[p]`, `π = p`, `e = p`: `‖x‖ = p^{−d}` (L7.10) ✓; [3] `e : ℝ` with `‖π‖ =
  e⁻¹` forces `e > 0`; no positivity hypothesis needed ✓; [5] `inv_zpow'`, `zpow_neg` ✓. SURVIVED.
- **L6.16** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_map_normAddValZ` — square
  `ℤ → ℝ`. Source Q4.5's pattern applied to `ℤ`, Q6.5/Q4.7 (base change of logarithms). D: `x = 0`:
  both `⊤` (`WithTop.map_top`); else `d` with `normAddValZ x = d` (`WithTop.ne_top_iff_exists`,
  L6.11), `‖x‖ = ‖π‖ ^ d` (L6.12), `normAddVal x = ↑(−log ‖x‖)` (L6.6), `Real.log_zpow`, `WithTop.map_coe`,
  `ring`.
  Attacks: [2] `x = π` ✓ (`1 · (−log ‖π‖)`); [5] `Real.log_zpow : log (x ^ n) = n * log x` ✓.
  SURVIVED.
- **L6.17** (leaf, Mathlib) `Normed.lean · NormedField.normAddValQ_zero`. D: `map_zero`. SURVIVED.
- **L6.18** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_top`. D: L4.12,
  `Valuation.zero_iff`. SURVIVED.
- **L6.19** (leaf, project) `Normed.lean · NormedField.normAddValQ_self`. Source Q4.2. D: L4.15.
  SURVIVED.
- **L6.20** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_of_pow_eq_pow` — the
  workhorse read off norms. Source Q4.3. D: L4.14 with `v x ≠ 0` from `hx` (`Valuation.zero_iff`),
  and `‖x‖₊ ^ n = ‖π‖₊ ^ m` from `h` (`NNReal.coe_inj`, `NNReal.coe_pow`, `coe_nnnorm`).
  Attacks: [2] `x = π`, `(1, 1)` ✓; [5] ✓. SURVIVED.
- **L6.21** (leaf, project) `Normed.lean · NormedField.norm_eq_norm_rpow_normAddValQ` —
  `‖x‖ = ‖π‖ ^ q`. Source Q6.4. D ([SRC]): `rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]; exact
  RankOne.hom_eq_rpow_addValQ _ π hq`.
  Attacks: [4] Q6.4 verbatim, "no exponential base and no factorisation hypothesis": the statement
  indeed has none ✓; [2] `q = 1` ✓; [5] L4.23 ✓. SURVIVED.
- **L6.22** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_map_normAddValQ`. Source Q4.5.
  D: L4.22 at `valuation`, `norm_eq_coe_hom K π`. SURVIVED ([5] ✓).
- **L6.23** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_map_normAddValZ`. Source Q4.5.
  D: L5.13. SURVIVED ([5] ✓).

### Internal node R6 ([6])

Every leaf is R3–R5 specialised to `NormedField.valuation` plus the two Mathlib identifications
`valuation_apply` and `hom' = embedding` (Q6.6). The one genuinely new argument is L6.9, whose
composition with L6.6/L6.7 is checked in its attacks. SURVIVED.

---

## Result R7 — `ℚ_p` (§1.3.5, `Padic.lean`)

### Plain-English proof (source: [RM] §1.3.5; [Kob84] I §2; [Mathlib] `Padic`)

Mathlib has `‖p‖ = p⁻¹`, `‖x‖ = p^{−x.valuation}` for `x ≠ 0`, `valuation p = 1` and
`Padic.addValuation x = x.valuation` for `x ≠ 0`. The value group of `NormedField.valuation` on
`ℚ_[p]` is generated by `g := ‖p‖₊`: every nonzero value `‖x‖₊` is `g ^ x.valuation` (from the
norm formula and `‖p‖₊ ^ k = (p⁻¹)^k`), and `g ∈ valueGroup`. So the value group is cyclic
(`IsCyclic`), it is nontrivial because the norm is (Mathlib's instance from `RankOne`), hence
`IsRankOneDiscrete` through `IsRankOneDiscrete.mk'`. The generator `< 1` is unique
(`genLTOne_unique_of_zpowers_eq`), so `generator = g = p⁻¹`, i.e. `p` is a uniformiser, hence a
normalising element (L5.4). Norm recovery at the uniformiser `p` with `‖p‖ = p⁻¹` (L6.15) gives
`‖x‖ = p^{−d}` for `normAddValZ x = d`; comparing with Mathlib's `‖x‖ = p^{−x.valuation}` and the
injectivity of `p ^ ·` gives `d = x.valuation`, so `normAddValZ ℚ_[p] x = Padic.addValuation x`
(both `⊤` at `0`).

### Shared quotes

> **Q7.1** [RM] §1.3.5: "**`ℚ_p`.** Prove that `NormedField.valuation` on `ℚ_[p]` is
> `IsRankOneDiscrete`, with value group generated by `‖p‖₊ = p⁻¹`, that `normAddValZ ℚ_[p] =
> Padic.addValuation` as additive valuations, and that `‖x‖ = p ^ (-(normAddValZ ℚ_[p] x))`."

> **Q7.2** [Kob84] I §2 (Q5.6): "|x|_p = p^{−ord_p x} if x ≠ 0; 0 if x = 0."

> **Q7.3** [Mathlib] `Padic.norm_eq_zpow_neg_valuation : x ≠ 0 → ‖x‖ = ↑p ^ (-x.valuation)`,
> `Padic.valuation_p : valuation ↑p = 1`, `Padic.norm_p : ‖↑p‖ = (↑p)⁻¹`, `Padic.addValuation.apply :
> x ≠ 0 → Padic.addValuation x = ↑x.valuation` (all elaborated in `names_pre.lean`).

### Leaves

- **L7.1** (leaf, Mathlib) `Padic.lean · Padic.nnnorm_p_eq_inv` — `‖(p : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹`.
  Source Q7.3. D: `rw [← NNReal.coe_inj]; push_cast; exact Padic.norm_p` ([SRC] `padic_nnnorm_p`).
  Attacks: [5] ✓; [2] n/a. SURVIVED.
- **L7.2** (leaf, Mathlib) `Padic.lean · Padic.nnnorm_p_ne_zero`. D: `rw [nnnorm_p_eq_inv];
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`. SURVIVED ([5] ✓).
- **L7.3** (leaf, Mathlib) `Padic.lean · Padic.nnnorm_p_zpow_valuation` — `‖p‖₊ ^ x.valuation =
  ‖x‖₊`. Source Q7.2/Q7.3. D ([SRC]): `← NNReal.coe_inj`, `push_cast`, `Padic.norm_eq_zpow_neg_valuation
  hx`, `Padic.norm_eq_zpow_neg_valuation (p ≠ 0)`, `Padic.valuation_p`, `← zpow_mul`, `ring_nf`.
  Attacks: [2] `x = p`: `‖p‖₊^1 = ‖p‖₊` ✓; [3] `hx` needed (`‖0‖₊ = 0` is no power) ✓; [5] ✓.
  SURVIVED.
- **L7.4** (leaf, Mathlib) `Padic.lean · Padic.zpowers_valueGroupGen` — `zpowers g = ⊤`. Source
  Q7.1 ("value group generated by `‖p‖₊`"). D ([SRC] `padic_zpowers_gen`): `Subgroup.eq_top_iff'`,
  `Subgroup.mem_zpowers_iff`, `valueGroup_eq_range`, L7.3 with `k = x.valuation`.
  Attacks: [1] an element of the value group not a power of `‖p‖₊` would need a norm outside
  `p^ℤ` — excluded by Mathlib's norm formula ✓; [5] ✓. SURVIVED.
- **L7.5** (leaf, Mathlib) `Padic.lean · Padic.isCyclic_valueGroup`. D:
  `isCyclic_iff_exists_zpowers_eq_top.mpr ⟨valueGroupGen, zpowers_valueGroupGen⟩`. SURVIVED ([5] ✓).
- **L7.6** (leaf, Mathlib) `Padic.lean · Padic.isRankOneDiscrete_valuation`. Source Q7.1. D:
  `inferInstance` — `IsRankOneDiscrete.mk'` from L7.5 and `Nontrivial (valueGroup …)`, which Mathlib
  derives from `IsNontrivial` (`Mathlib/RingTheory/Valuation/Basic.lean:614`), itself part of the
  `RankOne` instance of `NormedField.valuation` for a nontrivially normed field.
  Attacks: [5] the skeleton already *uses* this instance (`normAddValZ ℚ_[p]` elaborates in
  `Padic.lean`, `Examples.lean`), so instance search succeeds with L7.5 declared ✓; [2] n/a.
  SURVIVED.
- **L7.7** (leaf, Mathlib) `Padic.lean · Padic.coe_generator_eq` — `(generator : ℝ≥0) = p⁻¹`. D
  ([SRC] `padic_generator'_eq`, `padic_generator_eq`): `genLTOne_unique_of_zpowers_eq
  (generator'_lt_one _) (valueGroupGen < 1) (by rw [generator'_zpowers_eq_top, zpowers_valueGroupGen])`,
  then `nnnorm_p_eq_inv`.
  Attacks: [1] two generators `< 1` of the same cyclic group coincide — the cited lemma ✓;
  [5] `LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq` ✓. SURVIVED.
- **L7.8** (leaf, project) `Padic.lean · Padic.isUniformizer_p`. Source Q7.1 (uniformiser `p`
  implicit in "generated by `‖p‖₊`"), [Gou20] 6.4.4 (`π = p` for `e = 1`). D: `IsUniformizer.iff`;
  `Units.ext`-level: `valuation p = ‖p‖₊ = p⁻¹ = ↑generator` by L7.1, L7.7.
  Attacks: [2] n/a; [5] L7.7 ✓. SURVIVED.
- **L7.9** (leaf, project) `Padic.lean · Padic.isCommensurable_p`. D: `IsRankOneDiscrete.isCommensurable
  _ isUniformizer_p` (L5.4). SURVIVED ([5] ✓).
- **L7.10** (leaf, project) `Padic.lean · NormedField.norm_eq_zpow_neg_normAddValZ_padic` —
  `‖x‖ = p^{−d}`. Source Q7.1, Q7.2. D: `norm_eq_zpow_neg_normAddValZ_of_isUniformizer ℚ_[p]
  Padic.isUniformizer_p Padic.norm_p hd` (L6.15 with `e = p`).
  Attacks: [2] `x = p`, `d = 1` ✓; [5] L6.15 ✓. SURVIVED.
- **L7.11** (leaf, project) `Padic.lean · NormedField.normAddValZ_padic_apply`. Source Q7.1. D
  ([SRC] `normAddValZ_padic`): `x = 0`: `normAddValZ_zero`, `AddValuation.map_zero`; `x ≠ 0`: `d` from
  `WithTop.ne_top_iff_exists` (L6.11), `Padic.addValuation.apply hx`, `congr 1`, compare L7.10 with
  `Padic.norm_eq_zpow_neg_valuation hx` through `(zpow_right_strictMono₀ (1 < (p : ℝ))).injective`,
  `omega`.
  Attacks: [1] the two formulas `p^{−d} = p^{−val}` with `p > 1` force `d = val` — injectivity is
  the lemma cited ✓; [2] `x = 1`: `0 = 0` ✓; [5] `zpow_right_strictMono₀` ✓. SURVIVED.
- **L7.12** (leaf, project) `Padic.lean · NormedField.normAddValZ_padic` — **M3**, equality of
  additive valuations. Source Q7.1 ("as additive valuations"). D: `AddValuation.ext
  normAddValZ_padic_apply`. Attacks: [5] ✓; [6] n/a. SURVIVED.

### Internal node R7 ([6])

The chain is `IsCyclic → IsRankOneDiscrete → generator = p⁻¹ → p uniformiser → norm recovery →
agreement with Padic.addValuation`; each arrow is a leaf and the only external inputs are the
three Mathlib formulas of Q7.3. SURVIVED.

---

## Result R8 — Laurent series (§1.3.5, `LaurentSeries.lean`)

### Plain-English proof (source: [RM] §1.3.5 + Examples; [Mathlib] `LaurentSeries`; [BGR] 1.5.2)

Mathlib's `K⸨X⸩` carries the `X`-adic valuation `Valued.v := (idealX K).valuation` with values in
`ℤᵐ⁰`, surjective, with `v (single s 1) = exp (−s)` and `v (X ^ s) = exp (−s)`; [BGR] 1.5.2 says the
order function on `A⟦X⟧` defines a valuation precisely when `A` is a domain (here a field). A
nonzero `f` factors as `single f.order 1 * powerSeriesPart f` where the power-series part has
nonzero constant coefficient, hence valuation `1` (its valuation is `≤ 1`, and `≤ exp (−1)` would
force the constant coefficient to vanish); so `v f = exp (−f.order)`. The valuation is discrete:
its value group is a subgroup of `ℤᵐ⁰ˣ ≅ ℤ`, hence cyclic, and nontrivial; its generator is
`exp (−1)` (Mathlib, from surjectivity), so `X` is a uniformiser, `addValZ X = 1`, `addValZ (single s
1) = s`, and for `f ≠ 0`, `addValZ f = f.order` — "the order of vanishing at `t`" of [RM]'s example.
Stated for every field `K` (deviation D1 of `plan.md`): Mathlib's `K⸨X⸩` is `Valued`, not normed.

### Shared quotes

> **Q8.1** [RM] §1.3.5: "Prove the same for the Laurent-series field `𝔽_q⸨t⸩` at the uniformiser
> `t`." and Examples: "`𝔽_q⸨t⸩` at `t`: `normAddValZ` is the order of vanishing at `t`."

> **Q8.2** [Mathlib] `Mathlib/RingTheory/LaurentSeries.lean`: "The valuation of a Laurent series is
> the order of the first non-zero coefficient, see `valuation_le_iff_coeff_lt_eq_zero`";
> `valuation_single_zpow (s : ℤ) : Valued.v (single s 1) = exp (-s)`; `valuation_X_pow (s : ℕ) :
> Valued.v (X ^ s) = exp (-s)`; `valuation_surjective : Function.Surjective Valued.v`;
> `single_order_mul_powerSeriesPart : single x.order 1 * x.powerSeriesPart = x`.

> **Q8.3** [BGR] 1.5.2 Prop. 1 and Remark, p. 42: "Let `| |` denote the norm on `A[X]` (resp.
> `A⟦X⟧`) defined by the degree function deg (resp. by the order function ord), cf. (1.3.3). Then
> `| |` is a valuation if and only if `A` is an integral domain." — "The valuation `| | = α^{ord}`
> on `A⟦X⟧` is bounded but not trivial."

### Leaves

- **L8.1** (leaf, Mathlib) `LaurentSeries.lean · LaurentSeries.valuation_eq_exp_neg_order` — `v f =
  exp (−f.order)` for `f ≠ 0`. Source Q8.2 (the docstring sentence; Mathlib has only the `≤`
  characterisation), Q8.3. D: `conv_lhs => rw [← f.single_order_mul_powerSeriesPart]`; `map_mul`,
  `valuation_single_zpow`; `v (powerSeriesPart f : K⸨X⸩) = 1`: `le_antisymm ((idealX K).valuation_le_one
  _)` and `not_lt`: if `< 1` then `≤ exp (−1)` (in `ℤᵐ⁰`, `< 1 ↔ ≤ exp (−1)`: `WithZero.lt_one_iff`?
  — use `(intValuation_le_iff_coeff_lt_eq_zero K F (d := 1)).mp` to get `coeff 0 F = 0`, against
  `powerSeriesPart_coeff f 0 : coeff 0 F = f.coeff (f.order + 0)` and `HahnSeries.coeff_order_eq_zero.not.mpr
  hf`; `mul_one`.
  Attacks: [1] for `f = 0` the statement is false (`v 0 = 0 ≠ exp _`) — excluded by `hf` ✓; [2]
  `f = single s 1`: `order = s` (`HahnSeries.order_single`), consistent with Q8.2 ✓; `f = X`: `exp (−1)`
  ✓; [5] `single_order_mul_powerSeriesPart`, `valuation_single_zpow`, `powerSeriesPart_coeff` elaborate;
  `(idealX K).valuation_le_one` is used in Mathlib's own proofs in that file; the "`< 1 → ≤ exp (−1)`"
  step is the discreteness of `ℤᵐ⁰` (`WithZero.exp_le_exp`, `Int.lt_iff_add_one_le`) — the ticket
  spells it out. SURVIVED.
- **L8.2** (leaf, Mathlib) `LaurentSeries.lean · LaurentSeries.isRankOneDiscrete_valued`. Source
  Q8.1 ("the same" = discreteness, as for `ℚ_p`). D: `IsRankOneDiscrete.mk'` needs `IsCyclic
  (valueGroup …)` and `Nontrivial (valueGroup …)`. Nontrivial: Mathlib's instance from
  `IsNontrivial ((idealX K).valuation K⸨X⸩)` (`Valuation.IsNontrivial (v.valuation K)`,
  `AdicValuation.lean:401`), transported along `LaurentSeries.valuation_def` (`rfl`). Cyclic:
  `valueGroup ≤ ℤᵐ⁰ˣ`, and `ℤᵐ⁰ˣ` is cyclic (`isCyclic_of_surjective` along
  `WithZero.unitsWithZeroEquiv.symm : Multiplicative ℤ ≃* ℤᵐ⁰ˣ`, with `isCyclic_multiplicative` and
  `IsAddCyclic ℤ`), so `Subgroup.isCyclic` applies.
  Attacks: [1] a non-cyclic value group is impossible inside `ℤᵐ⁰ˣ ≅ ℤ` ✓; [5] `Subgroup.isCyclic`,
  `isCyclic_of_surjective`, `isCyclic_multiplicative`, `WithZero.unitsWithZeroEquiv` elaborate
  (`names_pre.lean`); whether Mathlib already provides the composite instance is tested first
  (`inferInstance`) — either way the leaf closes ✓; [3] any field `K` ✓. SURVIVED.
- **L8.3** (leaf, Mathlib) `LaurentSeries.lean · LaurentSeries.generator_valued_eq` — `generator =
  mk0 (exp (−1))`. D: `IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective (valuation_surjective
  K)`. Attacks: [5] the Mathlib lemma has exactly this statement for `v : Valuation R ℤᵐ⁰`
  surjective ✓; [4] generator `< 1` = `exp (−1)` ✓. SURVIVED.
- **L8.4** (leaf, project) `LaurentSeries.lean · LaurentSeries.isUniformizer_X`. Source Q8.1 ("at
  the uniformiser `t`"). D: `IsUniformizer.iff`; `rw [generator_valued_eq, Units.val_mk0]`;
  `simpa using valuation_X_pow K 1` (`pow_one`, `Nat.cast_one`).
  Attacks: [2] n/a; [5] L8.3, `valuation_X_pow` ✓. SURVIVED.
- **L8.5** (leaf, project) `LaurentSeries.lean · LaurentSeries.addValZ_X`. D: `addValZ_isUniformizer
  _ (isUniformizer_X K)` (L5.11). SURVIVED.
- **L8.6** (leaf, project) `LaurentSeries.lean · LaurentSeries.addValZ_single` — `addValZ (single s
  1) = s`. Source Q8.2. D: `addValZ_eq_of_zpow _ (isUniformizer_X K)` with `v (single s 1) = exp (−s)
  = (exp (−1)) ^ s = v X ^ s` (`valuation_single_zpow`, `valuation_X_pow K 1`, `WithZero.exp_zsmul`
  or `← WithZero.coe_zpow` with `ofAdd_zsmul`).
  Attacks: [2] `s = 0`: `single 0 1 = 1`, `addValZ 1 = 0` ✓; `s < 0` ✓ (zpow); [5] the `exp (−s) =
  exp (−1) ^ s` identity: `WithZero.exp_zsmul`-type lemma — verified in the ticket name check (the
  fallback `exp_neg`, `exp_zpow`/`coe_zpow` is spelled out in the ticket). SURVIVED.
- **L8.7** (leaf, project) `LaurentSeries.lean · LaurentSeries.addValZ_eq_order` — `addValZ f =
  f.order`. Source Q8.1 (Examples), Q8.2. D: `addValZ_eq_of_zpow _ (isUniformizer_X K)` with L8.1 and
  the same `exp (−s) = v X ^ s` identity at `s = f.order`.
  Attacks: [2] `f = X ^ n`: `order = n` ✓ (L11.7); [3] `hf` necessary (L8.1) ✓; [5] L8.1, L8.4 ✓.
  SURVIVED.

### Internal node R8 ([6])

L8.4–L8.7 compose L8.1/L8.3 with R5's uniformiser lemmas; the only seam is `Valued.v` versus
`(idealX K).valuation`, which is `rfl` (`valuation_def`). SURVIVED.

---

## Result R9 — extensions and completions (§1.3.6, §1.5.1–§1.5.3, `Extension.lean`)

### Plain-English proof (source: [RM] §1.3.6, §1.5.1–§1.5.3; [BGR] 3.2.4/2–3, 3.1.3, 1.5.1; [Gou20] 6.3–6.4, 6.8.7; [Kob84] III §2–§4)

**Restriction (§1.5.1).** For any normed `K`-algebra field `L`, `‖algebraMap K L x‖ = ‖x‖`
(Mathlib `norm_algebraMap'`), so `normAddVal L (algebraMap x) = −log ‖x‖ = normAddVal K x` for
`x ≠ 0`, and both are `⊤` at `0`. (Ultrametricity of `L` is Mathlib's `IsUltrametricDist.of_normedAlgebra`;
[BGR] 3.2.4/2 identifies the norm of an algebraic `L` over complete `K` with the spectral norm.)
**Ramification (§1.3.6).** Let `K`, `L` be discretely valued, `π` a uniformiser of `K`. In `L`,
`v_L (algebraMap π) = g_L ^ d` for some integer `d`, and `d > 0` since `‖algebraMap π‖ = ‖π‖ < 1`
and `g_L < 1`; `e := d` is the ramification index ([Gou20] 6.4.3: `v_p(K×) = (1/e)ℤ`, [BGR] 3.1.3).
For `x ∈ K` with `normAddValZ K x = k`, `‖x‖ = ‖π‖ ^ k` (L6.12), hence `‖algebraMap x‖ =
‖algebraMap π‖ ^ k`, i.e. `v_L (algebraMap x) = g_L ^ (e k)`, so `normAddValZ L (algebraMap x) =
e k` — [Kob84]'s `m = e · ord_p x`. Also `algebraMap π` is a normalising element of `L` (L5.3), and
for `y ∈ L` with `normAddValZ L y = d`, `(v_L y)^e = g_L^{de} = (v_L (algebraMap π))^d`, so
`normAddValQ L (algebraMap π) y = d / e`: `normAddValZ L = e · normAddValQ L (algebraMap π)`.
**Inheritance (§1.5.2).** For `K` complete and `L/K` algebraic, [BGR] 3.2.4/3: the minimal
polynomial `Xⁿ + ⋯ + a₀` of `x` has `|x|^n = |a₀|` (Mathlib: `‖x‖ = spectralNorm x =
‖a₀‖^{1/n}`). If `K` is commensurable at `π` and `x ≠ 0`, then `a₀ ≠ 0` and `|a₀|^k = |π|^m` for
some `k > 0`, so `|x|^{nk} = |algebraMap π|^m`: `L` is commensurable at `algebraMap π`. The
witnesses of an `x ∈ K` are witnesses of `algebraMap x` (same norms), so by the workhorse
`normAddValQ L (algebraMap π) (algebraMap x) = normAddValQ K π x`.
**Completion (§1.5.3).** In a valued field, every value of the completion is a value of the
field (Mathlib `Valued.exists_coe_eq_v`; [Gou20] Lemma 3.2.10/Prop. 6.8.7, [Kob84] III §4), and
`v (π : K̂) = v π`; so the commensurability witnesses of `K` serve for `K̂`.

### Shared quotes

> **Q9.1** [RM] §1.5.1: "For `L/K` an algebraic extension of a complete ultrametric normed field,
> normed by `spectralNorm.normedField`, prove `IsUltrametricDist L` and that the spectral norm
> extends the norm of `K`. Prove that `normAddVal L` restricts to `normAddVal K`."

> **Q9.2** [RM] §1.5.2: "**Commensurability is inherited.** If `NormedField.valuation` on `K` is
> `IsCommensurable` at `π`, so is the valuation of `L` at `algebraMap K L π`, and `normAddValQ L π`
> restricts to `normAddValQ K π`. The proof is from the definition of the spectral norm as a
> spectral value: `spectralNorm x ^ (n - i) = ‖aᵢ‖` for the index `i` realising the maximum over
> the coefficients of the minimal polynomial, so every value of `L` is commensurable with a value
> of `K`." (Route taken: the `i = 0` form `‖x‖ ^ n = ‖a₀‖`, which is Mathlib's
> `spectralNorm_eq_norm_coeff_zero_rpow` and [BGR] 3.2.4/3; same conclusion.)

> **Q9.3** [RM] §1.5.3: "**Completion preserves the value group.** For a rank-one valued field, the
> value group of the completion is the value group of the field, so `IsCommensurable` at `π`
> passes to the completion, and `normAddValQ` of the completion restricts to `normAddValQ` of the
> field."

> **Q9.4** [RM] §1.3.6: "**Finite extensions.** For `L/K` a finite extension of a complete discretely
> valued field, with `L` discretely valued under the spectral norm and ramification index
> `e(L/K)` — both cited from the local-fields-and-ramification roadmap — prove
> `normAddValZ L x = e(L/K) · normAddValZ K x` for `x ∈ K`, and identify `normAddValZ L` with
> `e(L/K)` times the `ℚ`-valued valuation of §1.4 normalised at a uniformiser of `K`."
> (Deviation D2 of `plan.md`: discreteness of `L` is a hypothesis and `e` is defined by
> `normAddValZ L (algebraMap K L π) = e`.)

> **Q9.5** [BGR] 3.2.4 Prop. 3, p. 140: "Let `K` be complete and let `q = X^m + a₁X^{m−1} + ⋯ + a_m
> ∈ K[X]` be irreducible. Then `σ(q) = |a_m|^{1/m}`; i.e., `|a_μ| ≤ |a_m|^{μ/m}` for all
> `μ = 1, …, m`." Proof: "Since `q` is the minimal polynomial of `θ₁, …, θ_m` over `K`, we have
> `|θ_μ| = σ(q)` for all `μ` by definition of the spectral norm. Since the spectral norm is a
> valuation on `L` by Theorem 2, the equation `a_m = (−1)^m ∏ θ_μ` yields `|a_m| = ∏ |θ_μ| =
> σ(q)^m`."

> **Q9.6** [BGR] 3.2.4 Thm 2, pp. 139–140: "Let `K` be complete with respect to the given valuation
> `| |`, and let `L` be an algebraic extension of `K`. Then the spectral norm on `L` is a valuation,
> and each power-multiplicative `K`-algebra norm on `L` coincides with this valuation. In
> particular, the spectral valuation is the unique valuation on `L` extending the valuation `| |`
> from `K`."

> **Q9.7** [Gou20] Def. 6.4.3, p. 193: "Let K/ℚ_p be a finite extension, and let e = e(K/ℚ_p) be
> the unique positive integer (dividing n = [K : ℚ_p]) defined by v_p(K×) = (1/e)ℤ. We call e the
> ramification index of K over ℚ_p." [BGR] 3.1.3 Prop. 2, p. 131: "For each valued ring `B`
> containing a valued subring `A` such that `|A − {0}|` is a group, we have `e(B/A) f(B/A) ≤
> rk_A B`."

> **Q9.8** [Gou20] p. 221 (PDFPAGE 224): "Recall that whenever we have a convergent sequence
> x_n → x ≠ 0 in a non-archimedean field, there exists an N such that |x_n| = |x| for n ≥ N (this
> is Lemma 3.2.10 …). This means that the set of possible absolute values in ℂ_p is exactly the
> same as in ℚ̄_p." [BGR] 1.5.1, p. 41: "The completion `(Â, | |^)` of a valued ring (resp. valued
> field) is a valued ring (resp. valued field)."

> **Q9.9** [Kob84] III §2, p. 61 (PDFPAGE 74): "We conclude that the norm of α equals the norm of
> each of its conjugates. But then the norm of N_{ℚ_p(α)/ℚ_p}(α), which is in ℚ_p, equals … =
> ‖α‖ⁿ. Thus ‖α‖ = |N_{ℚ_p(α)/ℚ_p}(α)|_p^{1/n}. So, concretely speaking, to find the p-adic norm of
> α, look at the monic irreducible polynomial satisfied by α. If it has degree n and constant term
> a_n, then the p-adic norm of α is the nth root of |a_n|_p."

### Leaves

- **L9.1** (leaf, Mathlib) `Extension.lean · Valued.isCommensurable_completion`. Source Q9.3, Q9.8.
  D: `constructor`; `val_pos`, `val_lt_one`: `Valued.valuedCompletion_apply π ▸ hπ.val_pos` etc.;
  `exists_zpow_eq x hx`: `obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x` (with `Valued.v x =
  extensionValuation x` by `rfl`), `hr : v x = v r`; `v r ≠ 0` from `hx`; `obtain ⟨m, n, hn, e⟩ :=
  hπ.exists_zpow_eq r this`; `⟨m, n, hn, by rw [hr, valuedCompletion_apply, e]⟩`.
  Attacks: [1] a value of the completion not attained on `K` would break this — Mathlib's lemma
  says there is none (nonarchimedean locally-constant norms, Q9.8) ✓; [2] `x = 0`: excluded by
  `hx` ✓; `x = (π : K̂)` ✓; [3] `Valued K Γ₀` for a *field* `K` is what `valuedCompletion` needs;
  no rank-one hypothesis needed — [RM]'s "rank-one valued field" is more than required ✓;
  [5] `Valued.exists_coe_eq_v`, `valuedCompletion_apply` ✓; the instance `Valued (Completion K) Γ₀`
  elaborates in the skeleton ✓. SURVIVED.
- **L9.2** (leaf, Mathlib) `Extension.lean · NormedField.normAddVal_algebraMap`. Source Q9.1 ("prove
  that `normAddVal L` restricts to `normAddVal K`"). D: `rcases eq_or_ne x 0 with rfl | hx`; zero:
  `map_zero`, `normAddVal_zero` twice; nonzero: `normAddVal_apply_of_ne_zero L (by simpa using hx)`,
  `normAddVal_apply_of_ne_zero K hx`, `norm_algebraMap'`.
  Attacks: [3] no completeness or algebraicity is needed (Q9.1 assumes both; the lemma holds for
  every normed `K`-algebra field — `norm_algebraMap'` only needs `NormOneClass L`) ✓;
  [2] `x = 1` ✓; [5] `norm_algebraMap'`, `(algebraMap K L).injective`/`map_ne_zero` ✓. SURVIVED.
- **L9.3** (leaf, project) `Extension.lean · NormedField.exists_normAddValZ_algebraMap_eq` — `e > 0`
  with `normAddValZ L (algebraMap π) = e`. Source Q9.4, Q9.7. D: `algebraMap π ≠ 0`; `d` from
  `WithTop.ne_top_iff_exists` (L6.11); `(addValZ_eq_iff _ _ d).mp` gives `v_L (algebraMap π) =
  ↑(generator ^ d)`; `v_L (algebraMap π) < 1` (`valuation_apply`, `norm_algebraMap'`, `hπ.val_lt_one`
  via `valuation_apply` on `K`); `generator < 1` (`generator_lt_one`); hence `0 < d`
  (`zpow_lt_one_iff_right_of_lt_one₀` on `Γ₀ˣ`-values coerced, or `Units.val_lt_val`); `⟨d.toNat,
  by omega, by rw [Int.toNat_of_nonneg hd.le]; exact hd⟩`.
  Attacks: [1] `e = 0` would mean `v_L (algebraMap π) = 1`, contradicting `‖π‖ < 1` ✓; [2] `L = K`:
  `e = 1` ✓; [3] both discreteness instances are used (`normAddValZ L`, `generator`) ✓; [5]
  `zpow_lt_one_iff_right_of_lt_one₀`, `Int.toNat_of_nonneg` — verified in the ticket name check.
  SURVIVED.
- **L9.4** (leaf, project) `Extension.lean · NormedField.normAddValZ_algebraMap` — **M4**, the
  ramification formula. Source Q9.4, [Kob84] Q5.4 ("`m = e · ord_p x`"), Q9.7. D: `rcases eq_or_ne
  x 0`; zero: both `⊤` (`WithTop.map_top`); nonzero: `k` with `normAddValZ K x = k`
  (`ne_top_iff_exists`), `‖x‖ = ‖π‖ ^ k` (L6.12), so `‖algebraMap x‖ = ‖algebraMap π‖ ^ k`
  (`norm_algebraMap'` twice); from `he` and `addValZ_eq_iff` on `L`: `v_L (algebraMap π) =
  ↑(generator_L ^ e)`; so `v_L (algebraMap x) = ↑(generator_L ^ (e * k))` (`valuation_apply`,
  `← NNReal.coe_inj`, `zpow_mul`, `Units.val_zpow_eq_zpow_val`); conclude `(addValZ_eq_iff _ _
  (e * k)).mpr`, `WithTop.map_coe`.
  Attacks: [1] without `he` the statement has no `e`; with `he` the integer `e` is forced
  (L9.3), so no inconsistency ✓; [2] `x = π`: `e * 1 = e` ✓ (`he` itself); `x = 1`: `0` ✓; [3] no
  finiteness, no completeness, no algebraicity: the argument only uses `‖algebraMap x‖ = ‖x‖` ✓
  (more general than Q9.4, which is for finite extensions); [4] Q9.4 "normAddValZ L x = e(L/K) ·
  normAddValZ K x for x ∈ K" ✓; [5] `zpow_mul`, `WithTop.map_coe` ✓. SURVIVED.
- **L9.5** (leaf, project) `Extension.lean · NormedField.isCommensurable_algebraMap_of_isRankOneDiscrete`.
  Source Q4.1 + Q9.4 (the normalising element of `L` used in the identification). D:
  `IsRankOneDiscrete.isCommensurable_of_lt_one _ h0 h1` (L5.3) with `h0 : v_L (algebraMap π) ≠ 0`
  (`map_ne_zero`, `hπ.ne_zero`) and `h1 : v_L (algebraMap π) < 1` (`valuation_apply`,
  `norm_algebraMap'`, `hπ.val_lt_one`).
  Attacks: [2] `L = K` ✓; [5] L5.3 ✓; [3] only discreteness of `L` and `0 < ‖π‖ < 1` enter ✓.
  SURVIVED.
- **L9.6** (leaf, project) `Extension.lean · NormedField.map_intCast_normAddValZ_eq_map_normAddValQ`
  — `Int.cast ∘ normAddValZ L = e · normAddValQ L (algebraMap π)`. Source Q9.4 (second sentence).
  D: `0 < e` from `he` as in L9.3; `rcases eq_or_ne y 0` (zero: both `⊤`); `d` with `normAddValZ L
  y = d`; `v_L y = ↑(g_L ^ d)` and `v_L (algebraMap π) = ↑(g_L ^ e)` (`addValZ_eq_iff`); so
  `v_L y ^ e = v_L (algebraMap π) ^ d` (`zpow_mul`, `mul_comm`); `addValQ_eq_of_zpow _ _ (v_L y ≠ 0)
  he_pos this : normAddValQ … y = ↑(d / e)`; finish with `WithTop.map_coe`, `WithTop.coe_inj`,
  `mul_div_cancel₀` (`(e : ℚ) ≠ 0`).
  Attacks: [1] for `e ≤ 0` the workhorse would not apply — but `he` forces `e > 0` (L9.3's
  argument, repeated inside) ✓; [2] `y = algebraMap π`: `e = e · 1` ✓; `y = 1`: `0 = e · 0` ✓;
  [3] the `IsCommensurable` instance is a hypothesis although derivable (L9.5) — `Prop`-class,
  all instances equal ✓; [5] `mul_div_cancel₀`, `WithTop.coe_inj` ✓. SURVIVED.
- **L9.7** (leaf, Mathlib) `Extension.lean · NormedField.norm_pow_natDegree_minpoly` — `‖x‖ ^ n =
  ‖a₀‖`. Source Q9.5 (BGR 3.2.4/3), Q9.9. D: `rw [NormedAlgebra.norm_eq_spectralNorm K x,
  spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div, Real.rpow_inv_natCast_pow (norm_nonneg
  _) (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne']`.
  Attacks: [1] for `K` not complete the norm of `L` need not be the spectral norm (two different
  extensions of a valuation) — `[CompleteSpace K]` is used by `NormedAlgebra.norm_eq_spectralNorm`
  ✓ (this is the D1 repair); [2] `x = 0`: `minpoly = X`, `n = 1`, `0 = 0` ✓; `x ∈ K`: `minpoly = X −
  x`, `‖x‖ = ‖−x‖` ✓; [3] `IsUltrametricDist K` is a hypothesis of Mathlib's lemma; `IsUltrametricDist
  L` is an unused section instance (cleanup may `omit` it) ✓; [4] Q9.5 is exactly `σ(q) =
  |a_m|^{1/m}` for the minimal polynomial; the roadmap's `i`-th coefficient form (Q9.2) is a
  different route to the same inheritance statement — recorded, not a drift of the *leaf* ✓;
  [5] `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `NormedAlgebra.norm_eq_spectralNorm`,
  `Real.rpow_inv_natCast_pow`, `minpoly.natDegree_pos` elaborate (`names_pre.lean`; the last two
  verified in the ticket name check). SURVIVED.
- **L9.8** (leaf, project) `Extension.lean · NormedField.isCommensurable_algebraMap` (instance) —
  **inheritance**. Source Q9.2, Q9.5, Q9.9. D: `constructor`; `val_pos`/`val_lt_one` via
  `valuation_apply`, `norm_algebraMap'`, `hπ.val_pos`/`val_lt_one`; `exists_zpow_eq x hx`: `x ≠ 0`;
  `a₀ := (minpoly K x).coeff 0 ≠ 0` (`minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x)
  hx`); `⟨m, k, hk, e⟩ := hπ.exists_zpow_eq a₀ (by simpa using this)`; `n := natDegree`, `hn : 0 <
  n`; from L9.7, `‖x‖₊ ^ n = ‖a₀‖₊` (`NNReal.coe_inj`, `coe_pow`); then `‖x‖₊ ^ ((n : ℤ) * k) =
  ‖a₀‖₊ ^ k = ‖π‖₊ ^ m = ‖algebraMap π‖₊ ^ m` (`zpow_mul`, `zpow_natCast`, `nnnorm_algebraMap'`);
  witnesses `⟨m, n * k, mul_pos (Nat.cast_pos.mpr hn) hk, …⟩`.
  Attacks: [1] counterexample to the *unfixed* statement (no completeness): see D1 — with
  `[CompleteSpace K]` the Mathlib identification holds ✓; algebraicity: for transcendental `L`
  (e.g. `K(T)` with `‖T‖ = p^{√2}`, completed) the conclusion fails, and `[Algebra.IsAlgebraic K L]`
  is used through `minpoly`/L9.7 ✓; [2] `L = K` ✓; `x = algebraMap π`: `minpoly = X − π`, `a₀ = −π`,
  witnesses `(m, k) = (1, 1)`, `n = 1` ✓; [3] every hypothesis is used ✓; [4] Q9.2 verbatim ("so is
  the valuation of `L` at `algebraMap K L π`") ✓; [5] `minpoly.coeff_zero_ne_zero`,
  `nnnorm_algebraMap'` — verified in the ticket name check. SURVIVED.
- **L9.9** (leaf, project) `Extension.lean · NormedField.normAddValQ_algebraMap` — restriction of
  `normAddValQ`. Source Q9.2 ("restricts to `normAddValQ K π`"). D: `rcases eq_or_ne x 0` (zero:
  both `⊤`); `⟨m, n, hn, e⟩ := (IsCommensurable at K).exists_zpow_eq x (by simpa using hx)`; `e' :
  v_L (algebraMap x) ^ n = v_L (algebraMap π) ^ m` by `valuation_apply`, `nnnorm_algebraMap'`;
  `rw [normAddValQ, normAddValQ, addValQ_eq_of_zpow _ _ _ hn e', addValQ_eq_of_zpow _ _ _ hn e]`.
  Attacks: [2] `x = π`: `1 = 1` ✓; [5] L4.13 ✓; [3] completeness/algebraicity are needed only to
  *state* it (the instance on `L`) ✓. SURVIVED.

### Internal node R9 ([6])

Three independent sub-results (restriction, ramification, inheritance) plus the completion
lemma; the only composition is L9.6 = L9.4's technique + L4.13, attacked above. SURVIVED.

---

## Result R10 — the algebraic closure of `ℚ_p`, and `ℂ_p` (§1.5.4–§1.5.5, `PadicComplex.lean`)

### Plain-English proof (source: [RM] §1.5.4–§1.5.5; [Kob84] III §3–§4; [Gou20] 6.8.6–6.8.7)

`ℚ_p` is complete and commensurable at `p` (L7.9), so every algebraic ultrametric normed
`ℚ_p`-algebra field is commensurable at `p` (L9.8 with `algebraMap p = p`) — in particular
`PadicAlgCl p` ([Kob84] III §3: `|α|_p = |a_n|_p^{1/n}`, a rational power of `p`). `ℂ_[p]` is the
completion of `PadicAlgCl p`; Mathlib's `Valued.v` on `ℂ_[p]` is the extended valuation and equals
`‖·‖₊` (through `norm_eq_norm`, `RankOne.hom_eq_embedding`), so L9.1 transports commensurability
at `p` to `ℂ_[p]` ([Gou20] 6.8.7: "the image of ℂ_p× under v_p is ℚ"). Hence `normAddValQ ℂ_[p] p`
exists with `normAddValQ p = 1`; on `x ∈ ℚ_p` with `x.valuation = k`, `‖x‖ = p^{−k} = ‖p‖^k` so the
workhorse gives `k`, i.e. `Padic.addValuation x`; `‖x‖ = ‖p‖^q = p^{−q}` (L6.21). Every rational
`q = a/b` is attained: `ℂ_p` is algebraically closed, so `z^b = p^a` has a solution ([Kob84] III §4:
"let `p^r` denote any root of `x^b − p^a`"), with `normAddValQ z = a/b`; and no other values than
rationals and `⊤` occur, by the type.

### Shared quotes

> **Q10.1** [RM] §1.5.4: "**The algebraic closure of `ℚ_p`, and `ℂ_p`.** Prove `IsCommensurable` at
> `p` for `PadicAlgCl p` and for `ℂ_[p]`, so that `normAddValQ ℂ_[p] p : AddValuation ℂ_[p]
> (WithTop ℚ)` is defined with `normAddValQ ℂ_[p] p p = 1`, restricts to `Padic.addValuation` on
> `ℚ_p`, and satisfies `‖x‖ = p ^ (-(normAddValQ ℂ_[p] p x))`."

> **Q10.2** [RM] §1.5.5: "Prove the value group of `ℂ_[p]` is exactly `p^ℚ`: every rational occurs
> as a valuation, and nothing else does."

> **Q10.3** [Kob84] III §4, p. 72 (PDFPAGE 85): "Finally, an arbitrary nonzero x ∈ Ω can be written
> as a fractional power of p times an element x₁ ∈ Ω of absolute value 1. Namely, if ord_p x = r =
> a/b (see Exercise 1 below), then let p^r denote any root of x^b − p^a = 0." Exercise 1, p. 73:
> "Prove that the possible values of | |_p on ℚ̄_p is the set of all rational powers of p (in the
> positive real numbers). What about on Ω? … What is the set of all possible values of ord_p on
> Ω?"

> **Q10.4** [Gou20] Prop. 6.8.7, p. 221 (PDFPAGE 224): "If x ∈ ℂ_p, x ≠ 0, then there exists a
> rational number v ∈ ℚ such that |x| = p^{−v}. In other words, the p-adic valuation v_p extends to
> ℂ_p, and the image of ℂ_p× under v_p is ℚ."

> **Q10.5** [Mathlib] `PadicComplex.valued : Valued ℂ_[p] ℝ≥0 := Valued.valuedCompletion`,
> `PadicComplex.norm_eq_norm (x : ℂ_[p]) : ‖x‖ = Valued.v.norm x`, `PadicComplex.RankOne.hom_eq_embedding`,
> `PadicComplex.norm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖ = ‖x‖`, `PadicComplex.coe_natCast`,
> `PadicComplex.isAlgClosed`; `PadicAlgCl.valued := NormedField.toValued`, `PadicAlgCl.valuation_def :
> Valued.v x = ‖x‖₊` (`rfl`).

### Leaves

- **L10.1** (leaf, project) `PadicComplex.lean · NormedField.isCommensurable_natCast_prime`
  (instance). Source Q10.1 (first half) via Q9.2. D: `have := isCommensurable_algebraMap (K :=
  ℚ_[p]) (L := L) (p : ℚ_[p])` (L9.8, instances `Padic.isCommensurable_p`, `CompleteSpace ℚ_[p]`);
  `rwa [map_natCast] at this`.
  Attacks: [3] `CompleteSpace ℚ_[p]` is a Mathlib instance ✓; `[Algebra.IsAlgebraic ℚ_[p] L]` is
  necessary (D1 counterexample) ✓; [2] `L = ℚ_[p]` ✓; [5] `map_natCast` ✓. SURVIVED.
- **L10.2** (leaf, project) `PadicComplex.lean · PadicAlgCl.isCommensurable_p`. Source Q10.1. D:
  `inferInstance` (L10.1; `PadicAlgCl.normedAlgebra`, `PadicAlgCl.isAlgebraic`,
  `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`).
  Attacks: [5] the four instances exist in `Mathlib/NumberTheory/Padics/Complex.lean` (lines
  59–122) ✓; [2] n/a. SURVIVED.
- **L10.3** (leaf, Mathlib) `PadicComplex.lean · PadicComplex.valuation_eq_nnnorm` — `Valued.v x =
  ‖x‖₊`. Source Q10.5 (the seam). D: `rw [← NNReal.coe_inj, coe_nnnorm, norm_eq_norm x,
  Valuation.norm_def, RankOne.hom_eq_embedding, Valuation.embedding_restrict]`.
  Attacks: [1] the `Valued` structure on `ℂ_[p]` could a priori differ from `NormedField.toValued`;
  Mathlib proves `norm_eq_norm` precisely to close this, and `hom = embedding` makes `Valued.v.norm x
  = (Valued.v x : ℝ)` ✓; [2] `x = 0` ✓; [5] names ✓ (`names_pre.lean`). SURVIVED.
- **L10.4** (leaf, project) `PadicComplex.lean · PadicComplex.normedField_valuation_eq`. D:
  `Valuation.ext fun x ↦ by rw [valuation_apply, valuation_eq_nnnorm]`. SURVIVED ([5] L10.3 ✓).
- **L10.5** (leaf, project) `PadicComplex.lean · PadicComplex.isCommensurable_p` (instance) — **ℂ_p
  is commensurable at `p`**. Source Q10.1, Q10.4, Q9.8. D: `have h₀ : (Valued.v : Valuation
  (PadicAlgCl p) ℝ≥0).IsCommensurable (p : PadicAlgCl p) := PadicAlgCl.isCommensurable_p`
  (`Valued.v = NormedField.valuation` by `PadicAlgCl.valuation_def`/`rfl`); `have h₁ :=
  Valued.isCommensurable_completion (K := PadicAlgCl p) (p : PadicAlgCl p)` (L9.1); `rw
  [normedField_valuation_eq]`; `simpa [PadicComplex.coe_natCast] using h₁` (the element
  `((p : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p])`).
  Attacks: [1] `ℂ_p` is not algebraic over `ℚ_p`, so L9.8 does not apply directly — the route is
  the completion lemma, as [RM] §1.5.3 prescribes ✓; [2] n/a; [3] no new hypothesis ✓;
  [4] Q10.1 "for `ℂ_[p]`" ✓; [5] `PadicComplex.coe_natCast`, `valuation_extends` ✓; the
  `UniformSpace.Completion (PadicAlgCl p)` of L9.1 is `ℂ_[p]` by definition (`abbrev PadicComplex`)
  ✓. SURVIVED.
- **L10.6** (leaf, project) `PadicComplex.lean · PadicComplex.normAddValQ_p` — `normAddValQ ℂ_[p] p p
  = 1`. Source Q10.1. D: `normAddValQ_self _ _` (L6.19). SURVIVED.
- **L10.7** (leaf, project) `PadicComplex.lean · PadicComplex.normAddValQ_algebraMap_padic` —
  restriction to `ℚ_p` is `Padic.addValuation`. Source Q10.1 ("restricts to `Padic.addValuation`
  on `ℚ_p`"). D: `rcases eq_or_ne x 0` (zero: `map_zero`, `AddValuation.map_zero`, `WithTop.map_top`);
  `k := x.valuation`; `Padic.addValuation.apply hx`, `WithTop.map_coe`; `normAddValQ_eq_of_zpow`-form:
  `addValQ_eq_of_zpow _ _ (v (algebraMap x) ≠ 0) one_pos` with `v (algebraMap x) ^ 1 = v p ^ k`:
  `‖algebraMap x‖₊ = ‖x‖₊ = ‖p‖₊ ^ k` (`norm_extends'`/`norm_algebraMap'`, `Padic.nnnorm_p_zpow_valuation`,
  `nnnorm_natCast`-style `‖(p : ℂ_[p])‖₊ = ‖(p : ℚ_[p])‖₊` via `PadicComplex.nnnorm_extends'`);
  `norm_num` (`k / 1 = k`).
  Attacks: [2] `x = p`: `1 = ↑1` ✓ (L10.6); `x = 1`: `0` ✓; [5] `Padic.addValuation.apply`,
  `PadicComplex.nnnorm_extends'` ✓. SURVIVED.
- **L10.8** (leaf, project) `PadicComplex.lean · PadicComplex.norm_eq_rpow_neg_normAddValQ` — `‖x‖
  = p^{−q}`. Source Q10.1, Q10.4. D: `rw [norm_eq_norm_rpow_normAddValQ _ _ hq]` (L6.21); `‖(p :
  ℂ_[p])‖ = (p : ℝ)⁻¹` (`norm_extends'`, `Padic.norm_p`, `map_natCast`); `Real.inv_rpow (by
  positivity)`, `← Real.rpow_neg (by positivity)`.
  Attacks: [2] `q = 1`: `p⁻¹` ✓; [5] `Real.inv_rpow`, `Real.rpow_neg` ✓. SURVIVED.
- **L10.9** (leaf, project) `PadicComplex.lean · PadicComplex.exists_normAddValQ_eq` — every
  rational occurs. Source Q10.2, Q10.3. D: `a := q.num`, `b := q.den`, `hb : 0 < b := q.den_pos`;
  `⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ a) hb` (`z ^ b = p ^ a`); `z ≠ 0`
  (`pow_ne_zero`-contrapositive: `p ^ a ≠ 0` as `(p : ℂ_[p]) ≠ 0`); `v z ^ (b : ℤ) = v p ^ a`
  (`map_pow`, `map_zpow₀`, `zpow_natCast`, `hz`); `addValQ_eq_of_zpow _ _ hz0 (by exact_mod_cast hb)
  this : normAddValQ z = ↑(a / b)`; `Rat.num_div_den q`.
  Attacks: [1] `ℂ_p` algebraically closed is Mathlib's `PadicComplex.isAlgClosed` ✓; [2] `q = 0`:
  `z ^ 1 = p ^ 0 = 1`, `z = 1`, value `0` ✓; `q = 1`: `z = p` ✓; negative `q` ✓ (zpow); [5]
  `IsAlgClosed.exists_pow_nat_eq`, `Rat.num_div_den`, `Rat.den_pos` — verified in the ticket name
  check. SURVIVED.
- **L10.10** (leaf, project) `PadicComplex.lean · PadicComplex.range_normAddValQ` — **M5**,
  `range = insert ⊤ (range (↑))`. Source Q10.2 ("every rational occurs … and nothing else does").
  D: `Set.ext fun y ↦ ?_`; `→`: `⟨x, rfl⟩`; `rcases eq_or_ne x 0`: `⊤` (`normAddValQ_zero`), else
  `WithTop.ne_top_iff_exists` (L6.18) gives `q` with `↑q = normAddValQ x`; `←`: `y = ⊤`: `⟨0,
  normAddValQ_zero _ _⟩`; `y = ↑q`: L10.9.
  Attacks: [2] both clauses exercised ✓; [3] none; [5] `Set.mem_insert_iff`, `Set.mem_range` ✓.
  SURVIVED.

### Internal node R10 ([6])

The chain `ℚ_p → PadicAlgCl p → ℂ_p` uses L9.8 then L9.1 with the seam L10.3/L10.4 between
`Valued.v` and `NormedField.valuation`; L10.6–L10.10 are R6 at `K = ℂ_[p]`, `π = p`. SURVIVED.

---

## Result R11 — the roadmap's examples (`Examples.lean`)

### Plain-English proof (source: [RM] Layer 1 Examples; [Kob84] I §2; [Gou20] Problems 242–244)

`normAddValZ p = 1` is L6.13 at the uniformiser `p`; `normAddValZ (1/p²) = −2` is `Padic.addValuation`
at `(p²)⁻¹` through L7.11 (Mathlib's `valuation_inv`, `valuation_pow`, `valuation_p`);
`normAddVal ℚ_[p] = log p · normAddValZ` is L6.16 with `−log ‖p‖ = log p`. In any algebraic
ultrametric normed `ℚ_p`-algebra field `L`, `s² = p` gives `‖s‖² = ‖p‖`, so the workhorse read off
norms gives `normAddValQ L p s = 1/2`; if `L` is discretely valued with `normAddValZ L s = 1`,
multiplicativity gives `normAddValZ L p = 2·1 = 2`. In `ℂ_p`, `x³ = p` gives `normAddValQ x = 1/3`.
For Laurent series, `addValZ (X ^ n) = n · addValZ X = n`.

### Shared quote

> **Q11.1** [RM] Layer 1, Examples: "`ℚ_p`: `normAddValZ p = 1`, `normAddValZ (1/p²) = -2`,
> `‖x‖ = p ^ (-v x)`, and `normAddVal ℚ_[p]` is `log p` times `normAddValZ`. `ℚ_p(√p)`:
> `normAddValZ` of the extension gives `√p ↦ 1` and `p ↦ 2`, while `normAddValQ` normalised at `p`
> gives `√p ↦ 1/2`. `ℂ_p` at `π = p`: `p^{1/3} ↦ 1/3`. `𝔽_q⸨t⸩` at `t`: `normAddValZ` is the order of
> vanishing at `t`."

### Leaves

- **L11.1** (leaf, project) `Examples.lean · NormedField.normAddValZ_padic_p`. D:
  `normAddValZ_isUniformizer _ Padic.isUniformizer_p` (L6.13, L7.8). SURVIVED ([5] ✓).
- **L11.2** (leaf, project) `Examples.lean · NormedField.normAddValZ_padic_inv_p_sq` — `= −2`. D:
  `rw [normAddValZ_padic_apply, Padic.addValuation.apply (by positivity-style: inv_ne_zero
  (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))), Padic.valuation_inv, Padic.valuation_pow,
  Padic.valuation_p]`; `norm_num`.
  Attacks: [2] n/a (a computation); [5] `Padic.valuation_inv`, `Padic.valuation_pow` elaborate
  (`names_pre.lean`) ✓; [4] Q11.1 "`normAddValZ (1/p²) = -2`" ✓. SURVIVED.
- **L11.3** (leaf, project) `Examples.lean · NormedField.normAddVal_padic` — `log p` times
  `normAddValZ`. D: `normAddVal_eq_map_normAddValZ ℚ_[p] Padic.isUniformizer_p x` (L6.16);
  `congr`/`funext`: `−Real.log ‖(p : ℚ_[p])‖ = Real.log p` by `Padic.norm_p`, `Real.log_inv`,
  `neg_neg`.
  Attacks: [2] `x = p`: `log p = 1 · log p` ✓; [5] `Real.log_inv` ✓. SURVIVED.
- **L11.4** (leaf, project) `Examples.lean · NormedField.normAddValQ_of_sq_eq_prime` — `1/2`. D:
  `normAddValQ_eq_of_pow_eq_pow L p (s ≠ 0) two_pos (m := 1)` with `‖s‖ ^ 2 = ‖s ^ 2‖ = ‖(p : L)‖ =
  ‖p‖ ^ 1` (`norm_pow`, `hs`, `pow_one`); `s ≠ 0` since `s ^ 2 = p ≠ 0` (`(p : L) = algebraMap ℚ_[p] L
  p` by `map_natCast`, `map_ne_zero`, `Nat.cast_ne_zero`); `norm_num`.
  Attacks: [2] `L = ℚ_[p](√p)` is the intended instance; the statement holds in any `L` with
  such an `s` ✓; [3] the instance `isCommensurable_natCast_prime` supplies commensurability ✓;
  [5] `norm_pow` ✓. SURVIVED.
- **L11.5** (leaf, project) `Examples.lean · NormedField.normAddValZ_prime_of_sq_eq_prime` —
  `normAddValZ L p = 2` from `normAddValZ L s = 1`. D: `rw [← hs, AddValuation.map_pow, h1,
  two_nsmul, one_add_one_eq_two]`.
  Attacks: [3] without `h1` the conclusion is false (e.g. an unramified `L` with `s ∉ L` cannot
  occur, but `s` a uniformiser of a ramified `L` with `normAddValZ L s = 1` is what Q11.1 means
  by "`√p ↦ 1`") ✓; [2] n/a; [5] `two_nsmul`, `one_add_one_eq_two` ✓. SURVIVED.
- **L11.6** (leaf, project) `Examples.lean · NormedField.normAddValQ_padicComplex_of_pow_three` —
  `1/3`. D: as L11.4 with `n = 3`, `norm_pow`, `norm_extends'`-free since `‖x ^ 3‖ = ‖(p : ℂ_[p])‖`
  directly; `x ≠ 0` from `(p : ℂ_[p]) ≠ 0` (`Nat.cast_ne_zero`, `CharZero ℂ_[p]`).
  Attacks: [2] ✓; [5] `PadicComplex.charZero` ✓. SURVIVED.
- **L11.7** (leaf, project) `Examples.lean · LaurentSeries.addValZ_X_pow` — `n`. D: `rw
  [AddValuation.map_pow, addValZ_X, nsmul_one]`? — `n • (1 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`:
  `nsmul_eq_mul`, `mul_one`, `Nat.cast`-coherence (`WithTop.coe_natCast`), spelled out in the
  ticket.
  Attacks: [2] `n = 0`: `addValZ 1 = 0` ✓; [5] `AddValuation.map_pow` ✓. SURVIVED.

---

## Confidence gate (Step 5)

1. **Every leaf discharged**: 144 declarations; each leaf above names its Mathlib lemmas (verified
   by elaboration) or the project leaf it reduces to. No API gap is open: the only new
   mathematical content beyond [SRC] (L2.6, L4.19, L5.3, L8.1–L8.7, L9.1–L9.9, L10.1–L10.10, the
   examples) decomposes to Mathlib lemmas named above.
2. **Skeleton compiles**: `lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples`, 2884 jobs,
   `sorry` warnings only; `scratch/signatures.txt` has 143 elaborated signatures, 0 errors.
3. **Verbatim quotes + Lean ↔ source match**: every leaf cites a shared quote Q*.* (verbatim from
   [RM]/[Kob84]/[Gou20]/[BGR]/[PR]/[Mathlib]) and states the match in its D/attack lines.
4. **Adversarial pass**: every leaf has an attacks block with ≥ 3 categories; every internal node
   has a composition attack; one defect (D1) found and repaired.
5. **Prior-B2 log**: consulted (table above); no name match; the dropped-variable shape caught D1.
6. **Mirrors the source**: the roadmap's clause structure is the tree (R1 = §1.1, R2–R4 = §1.4 with
   its group-theoretic substrate, R5 = §1.3.1–3, R6 = §1.2.2–3/§1.3.4/§1.4.6, R7–R8 = §1.3.5,
   R9 = §1.3.6/§1.5.1–3, R10 = §1.5.4–5, R11 = Examples); where the roadmap defers to a source
   ([Kob84], [Gou20], [BGR]) the quotes are from that source. Sizing: every leaf is a one-paragraph
   argument in its source and a ≤ 15-line Lean proof in [SRC] where ported; the tickets' sketches
   are grounded in those.
7. **Single-conclusion**: checked above (only shared-witness existentials).

No REVIEW-PENDING leaves (the ChatGPT MCP server was unavailable; no step needed it — every
source gap was closed by [Kob84]/[Gou20]/[BGR]).

## Feasibility

The layer is a port of a sorry-free development ([SRC], §1.1–§1.4 and `ℚ_p`) with the [PR] names,
plus five new pieces, each discharged from named Mathlib lemmas: the uniqueness statement §1.4.4
(L2.6/L4.19, elementary), discreteness/uniformiser/order for Laurent series (L8.1–L8.7, from
Mathlib's `LaurentSeries` valuation API), the ramification formula §1.3.6 (L9.3–L9.6, from norm
extension and the generator characterisation), inheritance of commensurability §1.5.2 (L9.7–L9.9,
from Mathlib's `NormedAlgebra.norm_eq_spectralNorm` and `spectralNorm_eq_norm_coeff_zero_rpow`) and
`ℂ_p` (L9.1 + L10.*, from `Valued.exists_coe_eq_v` and `IsAlgClosed.exists_pow_nat_eq`). The
recorded deviations D1–D6 of `plan.md` are statement-level and visible to the roadmap's reader.
Expected size: 52 proof tickets, none longer than a working session.
