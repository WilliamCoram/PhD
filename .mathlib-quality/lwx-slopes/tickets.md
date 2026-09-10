# Ticket Board — lwx-slopes ([LWX] §3.23 Step II, §4.1–4.2, coefficient level)

**BOARD PATH: `.mathlib-quality/lwx-slopes/`** (see `plan.md`; `decomposition.md` has the
verbatim source quotes and attack logs per leaf; `renames.jsonl` / `b2_log.jsonl` live here).

## Summary
- Total: 81 tickets — 57 proof/def tickets + 24 cleanup tickets
- Open: 0 | In Progress: 0 | Done: 81 — **ALL DONE (2026-09-05, one beastmode session)**
- Milestones: **V17/V18** (Theorem 1.3's `X_k` / `X_{(k,k+1)}` slope reading, conditional on
  `HasUnitBand`) and **P4** (Theorem 1.5 (1.5.1) at the polygon level, conditional on
  `HasUnitBand` at every `k`)
- Parallel capacity: 3 at start (NP ∥ S ∥ U), then C after S+U, V after NP+S+U, P last

## Conventions (binding, inherited from lwx-halo)
- Statements below are **verbatim from the skeleton**; `/beastmode` fills the `sorry` at the
  cited `file:line` (line numbers as of 2026-09-05; search by name if they drift).
- `lia` → `omega`; every ticket: `lake build PhD.<Module>` clean, no `sorry`, standard axioms
  (`propext`/`Classical.choice`/`Quot.sound`); `lake exe runLinter PhD.<Module>` clean on the
  file's own declarations at every CLEANUP; renames/statement-fixes to `renames.jsonl`,
  B2 stops to `b2_log.jsonl` (this directory).
- Never edit `PhD/LWX/Halo.lean`, the NewtonPolygons library, or `PhD/PR'd/`; new helpers go
  in the six board files.
- Common hypotheses (abbreviated `HYP` below):
  `(hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K)
  (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)`;
  `HYPκ` = `HYP` + `[Nonempty ι]` + `(hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))`;
  `NP_T` = `newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)`;
  `vT` = `-Real.log ‖T₀‖`; `t` = `Fintype.card ι`; `b n m` = `(charCoeff (D.op ω) n) m`.

## Dependency chains
```
NP1 → NP2 ; NP3, NP4 independent ; NP5 (via Height.lean's `toReal_unitSlope_le`)   [Support.lean]
S1 → S2 ; S3, S4, S5 → S6 ; S2+S5+S6 → S7 ; S3+S4+S5 → S8 ; S7+S8 → S9   [Sharpness.lean]
U1 → U3 ; U2 → U4 → U5 (U3) → U6 ; U1 → U7, U8 ; U6+U7 → U9 ; U6+U8 → U10 ;
U2 → U11 → U12 → U13 → U14                                          [UpperPolygon.lean]
V1 ; V2, V3 → V4 ; U12 → V5 ; V6 ; S7 → V7 ; S8 → V8 ;
NP2+V2+V3+V5+V6+V7+U13 → V9 ; NP1+V2+V5+V6+V8+U13 → V10 ; NP1+V3+… → V11 ;
V9 → V12 ; NP1+V1+V5+V6+V8+U13 → V13 ; V9+NP3+NP4 → V14 ; V9+V11+NP3+NP4 → V15 ;
V9+V10+NP3+NP4 → V16 ; V14+V15+V16 → V17 ; V4+V15+V16 → V18         [Vertices.lean]
C1 → C2 ; C3 ; S1+S2+S3+S4+U10+C1+C3 → C4 → C5 → C7 ; S2+S3+S4+S5+C2+C3+U10 → C6  [Claim.lean]
C2 → P1 → P2 (U4, U5) ; NP4+NP5+P1+P2+V12+C6+C7 → P3 → P4 (NP3, NP4)  [SlopeRatios.lean]
Cleanup cadence: CL-NP1 after NP3, CL-NP2 after NP5; CL-S1 after S3, CL-S2 after S6,
CL-S3 after S9; CL-U1..U4 after U3/U6/U9/U12, CL-U5 after U14; CL-V1..V5 after
V3/V6/V9/V12/V15, CL-V6 after V18; CL-C1 after C3, CL-C2 after C6, CL-C3 after C7;
CL-P1 after P3, CL-P2 after P4; CLEANUP-ALL-1 before V17; CLEANUP-ALL-2 before P4;
CLEANUP-FINAL last.
```

---

## Tranche NP — `PhD/NewtonPolygons/Support.lean`

Planning audit (2026-09-05, at the user's request): `Height.lean` already holds the
height/unit-slope dictionary — `height_eq_heightFun` + the definition of `heightFun`
(`y₀ + ∑ toReal (unitSlope i)`), `heightFun_succ`, `unitSlope_ne_top_of_height_ne_top`, and,
**as `private` lemmas**, `unitSlope_eq_top_of_height_eq_top` (Height.lean:542) and
`toReal_unitSlope_le` (Height.lean:658); `OfSlopes.lean:170` holds, also `private`, the
`⊥`-exclusion `slopes_zero_ne_bot` for constructed polygons.  Two planned lemmas were therefore
dropped as redundant, one was found **false** (a finite height does not exclude a `⊥` unit slope:
the degenerate one-point polygon has `height 1 = y₀`), and the tranche now contains only what is
genuinely absent.  **Decision (user, 2026-09-05)**: the three `private` lemmas were made public
(`renames.jsonl`) — "if they are needed multiple times, this signals they probably should be
global API"; NP4/NP5/V15 use them directly.

### [NP1] The competitor lemma
- **Status**: done (finished 2026-09-05T12:40Z) | **File**: PhD/NewtonPolygons/Support.lean:71 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem twoSlope_le_height (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    {y₀ s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {N : ℕ}
    (hpts : ∀ n : ℕ,
      ((y₀ + s₁ * min (n : ℝ) N + s₂ * max ((n : ℝ) - N) 0 : ℝ) : WithBotTop ℝ) ≤
        pointHeight v n)
    (k : ℕ) :
    ((y₀ + s₁ * min (k : ℝ) N + s₂ * max ((k : ℝ) - N) 0 : ℝ) : WithBotTop ℝ) ≤
      P.height k := by sorry
```
#### Proof sketch
1. Define the competitor `Q := NewtonPolygon₀.ofSlopes (fun i => if i < N then s₁ else s₂) hmono y₀`,
   where `hmono` is `Monotone` from `hs` (`fun a b hab => by split_ifs <;> linarith`-style;
   the only nontrivial case `a < N ≤ b` is `hs`).
2. Compute `Q.height k` by `NewtonPolygon₀.height_ofSlopes`: `y₀ + ∑ i ∈ range k, if i < N then s₁ else s₂`
   `= y₀ + s₁ * min k N + s₂ * max (k − N) 0` — split the sum with `Finset.sum_ite`,
   `Finset.filter_lt_eq_Ico`/`card_range`, and `Nat.cast` the counts (`min`/`max` case split on `k ≤ N`).
3. `h.isGreatest Q (by rw [ofSlopes_starting_point, hx]) (fun n => by rw [hQ n]; exact hpts n)`
   gives `Q.IsBelow P`; `NewtonPolygon₀.isBelow_iff_height` at `k` plus step 2 closes.
#### Mathlib lemmas needed
`Finset.sum_ite`, `Finset.filter_lt` (or `Finset.sum_range_add` split at `min k N`), `Finset.card_range`,
`Finset.sum_const`, `smul_eq_mul`, `min_def`/`max_def`; project: `NewtonPolygon₀.ofSlopes`,
`ofSlopes_starting_point`, `height_ofSlopes`, `IsNewtonPolygonOf.isGreatest`, `isBelow_iff_height`.
#### Sources
[LWX, p. 26] "the diﬀerences in all strict inequalities are at least min{v(T), 1−v(T)}" — the
margin this lemma propagates from points to the polygon; the specification `IsNewtonPolygonOf`
(PhD/NewtonPolygons/Spec.lean:61, "greatest convex minorant").  The same `isGreatest`+`ofSlopes`
pattern is done inline in Halo.lean:243 and QMF/Weight/Slopes.lean:184 — this is its reusable form.
Source lines: 2 (LWX) + the spec docstring; est. 45 LOC.
#### Generality decision
`Γ = ℝ`, anchor `0` (the only case used; general anchors would just shift `k`).  Two slopes
suffice for every use on this board (breaks at `n_k^±`, `n_k ± 1`).

### [NP2] Supporting lines
- **Status**: done (finished 2026-09-05T12:50Z) | **File**: PhD/NewtonPolygons/Support.lean:82 | **Depends on**: NP1
- **Parallel**: after NP1 | **Type**: lemma
#### Statement
```lean
theorem line_le_height (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0) {a b : ℝ}
    (hpts : ∀ n : ℕ, ((a + b * n : ℝ) : WithBotTop ℝ) ≤ pointHeight v n) (k : ℕ) :
    ((a + b * k : ℝ) : WithBotTop ℝ) ≤ P.height k := by sorry
```
#### Proof sketch
1. `have := h.twoSlope_le_height hx (le_refl b) (N := 0) (y₀ := a) ?_ k`; simplify
   `min (n:ℝ) 0 = 0`, `max (n − 0) 0 = n` (`n ≥ 0`) with `min_eq_right`, `max_eq_left`, `Nat.cast_nonneg`.
2. Feed `hpts` after the same simplification.
#### Mathlib lemmas needed
`min_eq_right`, `max_eq_left`, `Nat.cast_nonneg`, `sub_zero`, `mul_zero`, `add_zero`.
#### Sources
Same as NP1 (the `μ = 0` instance).  est. 15 LOC.
#### Generality decision
Corollary of NP1; kept as its own name because V9/V13 use it repeatedly.

### [NP3] Unit slope = height increment
- **Status**: done (finished 2026-09-05T12:50Z) | **File**: PhD/NewtonPolygons/Support.lean:42 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem unitSlope_eq_of_height_eq (hx : P.starting_point.1 = 0) {j : ℕ}
    (hb : P.unitSlope j ≠ ⊥) {a c : ℝ} (hj : P.height (j : ℤ) = (a : WithBotTop ℝ))
    (hj1 : P.height ((j + 1 : ℕ) : ℤ) = (c : WithBotTop ℝ)) :
    P.unitSlope j = ((c - a : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. `height_eq_heightFun` at `j` and `j+1` (both `≠ ⊤`; rewrite `(j : ℤ) = P.starting_point.1 + j`
   with `hx`), so `a = heightFun j`, `c = heightFun (j+1)` (`WithBotTop.coe_inj`).
2. `heightFun_succ`: `c = a + toReal (unitSlope j)`.
3. `unitSlope j ≠ ⊤` (`unitSlope_ne_top_of_height_ne_top` with `c := j+1`) and `≠ ⊥` (`hb`), so
   `unitSlope j = (toReal (unitSlope j) : WithBotTop ℝ)` (case on `WithBotTop`, `toReal_coe`); conclude.
#### Mathlib lemmas needed
`WithBotTop.coe_inj` (repo), `sub_eq_iff_eq_add`; project: `height_eq_heightFun`, `heightFun_succ`,
`unitSlope_ne_top_of_height_ne_top`, `NewtonPolygon.toReal_coe`.
#### Sources
Height.lean:76 (`heightFun_succ`).  The `⊥` hypothesis is forced by the degenerate one-point polygon
(`slopes 0 = ⊥`, `lengths 0 = 0`): its heights are `y₀, y₀, ⊤, …`, so with `a = c = y₀` the
conclusion `⊥ = ↑0` would be false — found at planning by reading `rightHeight`'s junk guard.  est. 25 LOC.
#### Generality decision
Anchor `0`, real values; `hb` is supplied by NP4 for every polygon on this board.

### [CL-NP1] /cleanup on PhD/NewtonPolygons/Support.lean (cadence)
- **Status**: done (finished 2026-09-05T13:10Z, inline with CL-NP2) | **Depends on**: NP1, NP2, NP3 | **Blocks**: NP4, NP5 | **Type**: cleanup

### [NP4] No `⊥` unit slopes on constructed polygons
- **Status**: done (finished 2026-09-05T12:50Z) | **File**: PhD/NewtonPolygons/Support.lean:60 | **Depends on**: CL-NP1
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem newtonPolygon₀OfSeq_unitSlope_ne_bot (v : ℕ → WithTop ℝ) (h1 : ∃ i, v i ≠ ⊤)
    (h2 : IsAdmissible v) (j : ℕ) : (newtonPolygon₀OfSeq v).unitSlope j ≠ ⊥ := by sorry
```
#### Proof sketch
`intro hbot`; `(slopes_zero_eq_bot_of_unitSlope_eq_bot hbot).1 : slopes 0 = ⊥` contradicts
`slopes_zero_ne_bot v h1 h2` (OfSlopes.lean:170, public since 2026-09-05; it is stated exactly for
this purpose: "The first slope of the polygon constructed from an admissible sequence is not `⊥` …
(Stated here, against the construction, rather than in the Newton-polygon files)").
#### Mathlib lemmas needed
none; project: `slopes_zero_eq_bot_of_unitSlope_eq_bot`, `slopes_zero_ne_bot` (OfSlopes.lean:170).
#### Sources
The `Step.unboundedBelow` case of the construction (Construction.lean:19–33) and `IsAdmissible`
(SpecConstruction.lean:43).  est. 5 LOC.
#### Generality decision
Stated for `Γ = ℝ` (all board polygons); the library lemma is `Γ`-generic.

### [NP5] Monotone real unit slopes
- **Status**: done (finished 2026-09-05T12:50Z) | **File**: PhD/NewtonPolygons/Support.lean:50 | **Depends on**: CL-NP1
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem monotone_toReal_unitSlope (hx : P.starting_point.1 = 0)
    (hfin : ∀ k : ℕ, P.height k ≠ ⊤) :
    Monotone fun j => NewtonPolygon.toReal (P.unitSlope j) := by sorry
```
#### Proof sketch
`fun i j hij => P.toReal_unitSlope_le hij (P.unitSlope_ne_top_of_height_ne_top (hfin (j+1)) (Nat.lt_succ_self j))`
after rewriting `(j+1 : ℤ) = starting_point.1 + (j+1)` with `hx`.  `toReal_unitSlope_le`
(Height.lean:658, public since 2026-09-05) already handles the `⊥` arm via `unitSlope_eq_bot_cases`.
#### Mathlib lemmas needed
`Monotone`, `Nat.lt_succ_self`; project: `toReal_unitSlope_le`, `unitSlope_ne_top_of_height_ne_top`.
#### Sources
Height.lean:658 (public since 2026-09-05).  est. 5 LOC.
#### Generality decision
As NP3.
- **Progress (NP1–NP5, CL-NP1/2)**: 2026-09-05T12:40Z NP1 compiled first try: private
  `monotone_twoSlope` + `sum_twoSlope` (induction on `k`, `min`/`max` case split on `k < N`
  with `linarith`-discharged side conditions), then `set Q := ofSlopes …`, `height_ofSlopes`,
  `h.isGreatest`, `isBelow_iff_height`. NP2: `twoSlope_le_height` at `N = 0` after a `hsimp`
  rewriting `min n 0`/`max (n − 0) 0`. NP3: `height_eq_heightFun` twice (after `rw [hx, zero_add]`),
  `heightFun_succ`, `WithBotTop.coe_le_coe` antisymmetry for coe-injectivity (`simpa` does NOT
  reduce `WithBotTop.coe a = WithBotTop.coe b`), real extraction by `generalize` +
  `induction w using WithBotTop.rec`. NP4: two-liner via `slopes_zero_ne_bot` +
  `slopes_zero_eq_bot_of_unitSlope_eq_bot`. NP5: `toReal_unitSlope_le` +
  `unitSlope_ne_top_of_height_ne_top (c := j + 1)`. Cleanup done inline (user rejected
  Agent-dispatched workers): docstring title de-skeletoned, four over-wide docstring lines
  wrapped (≤ 100 codepoints), lambdas `=>` → `↦` (match arms keep `=>`), private helpers'
  docstrings stripped; `lake build PhD.NewtonPolygons.Support` clean (1873 jobs),
  `lake exe runLinter` clean, all five decls on `propext`/`Classical.choice`/`Quot.sound`.

### [CL-NP2] /cleanup on PhD/NewtonPolygons/Support.lean (final)
- **Status**: done (finished 2026-09-05T13:10Z) | **Depends on**: NP4, NP5 | **Type**: cleanup

---

## Tranche S — `PhD/LWX/Sharpness.lean`

### [S1] Strict ultrametric bound for a null family
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:38 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_tsum_lt_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {B : ℝ} (hB : 0 < B)
    (hlt : ∀ i, ‖f i‖ < B) : ‖∑' i, f i‖ < B := by sorry
```
#### Proof sketch
1. `Metric.tendsto_nhds.1 hf (B/2) (by positivity)` + `Filter.eventually_cofinite` ⟹ the set
   `S := {i | ¬ ‖f i‖ < B/2}` is finite.
2. `TateFredholm.norm_tsum_le_iSup hf` bounds `‖∑'‖` by `⨆ i, ‖f i‖`; `ciSup_le` reduces to a
   bound per `i`: if `i ∉ S` then `< B/2 ≤ M`, else `≤ M` where `M := max (B/2) (S.toFinset.sup' … ‖f ·‖)`
   (`Finset.exists_max_image` if `S` nonempty, else `M = B/2`).
3. `M < B`: each `‖f i‖ < B` (`hlt`) and `B/2 < B`.
#### Mathlib lemmas needed
`Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.toFinset`, `Finset.exists_max_image`
(or `Finset.sup'_lt_iff`), `ciSup_le`, `half_lt_self`; project: `TateFredholm.norm_tsum_le_iSup`
(Tate.lean:445; note `bddAbove` of the range is inside that proof — mirror it).
#### Sources
[LWX, p. 23] "The rest of the corollary is clear" (the strict ultrametric principle); decomposition
S1.  est. 40 LOC.
#### Generality decision
Arbitrary index type, complete ultrametric normed group (same section variables as
`norm_tsum_le_iSup`); namespace `TateFredholm` (upstream candidate).

### [S2] Unique dominant term
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:44 | **Depends on**: S1
- **Parallel**: after S1 | **Type**: lemma
#### Statement
```lean
theorem norm_tsum_eq_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {i₀ : ι} {B : ℝ}
    (hi₀ : ‖f i₀‖ = B) (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < B) : ‖∑' i, f i‖ = B := by sorry
```
#### Proof sketch
1. `Summable f` from `TateFredholm.summable_of_tendsto_cofinite hf`; `Summable.tsum_eq_add_tsum_ite`
   splits `∑' = f i₀ + ∑' i, if i = i₀ then 0 else f i`.
2. `hB : 0 < B` or `B = 0`: if `B = 0` then every `i ≠ i₀` has `‖f i‖ < 0` — impossible — so the
   `ite` family is identically `0` and the sum is `f i₀`; else S1 on the `ite` family
   (`Tendsto` of the modified family from `hf` via `Filter.Tendsto.congr'`/squeeze, each term
   `< B`) gives `‖rest‖ < B = ‖f i₀‖`.
3. `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (norms differ) ⟹ `‖f i₀ + rest‖ = max = B`.
#### Mathlib lemmas needed
`Summable.tsum_eq_add_tsum_ite`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `max_eq_left`,
`tsum_zero`/`tsum_congr`; project: `summable_of_tendsto_cofinite`, S1.
#### Sources
[LWX, p. 23] "with equality holding if and only if m = λ(n) and bn,λ(n) is a p-adic unit"; decomposition S2.  est. 45 LOC.
#### Generality decision
As S1.

### [S3] (3.18.1), the case `m < λ(n)`
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:61 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_coeff_mul_zpow_le_of_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : m < lwxLambda p (Fintype.card ι) n) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * ((p : ℝ)⁻¹ / ‖T₀‖) := by sorry
```
#### Proof sketch
1. `norm_mul, hψ, norm_zpow`; `norm_coeff_charCoeff_upOp_le hp2 D ω n m : ‖b‖ ≤ p^(m − λ)`.
2. With `d := λ − m ≥ 1` (as `ℤ`): `p^(m−λ)·‖T₀‖^m = ‖T₀‖^λ · (p⁻¹/‖T₀‖)^d` (`zpow_sub₀`,
   `zpow_neg`, `div_zpow`, `mul_zpow`, `zpow_add₀` with `‖T₀‖ ≠ 0`).
3. `(p⁻¹/‖T₀‖)^d ≤ (p⁻¹/‖T₀‖)^1` since `0 < p⁻¹/‖T₀‖ < 1` (`div_lt_one`, `h0`) and `1 ≤ d`
   (`zpow_le_zpow_right_of_le_one₀`), then `zpow_one`.
#### Mathlib lemmas needed
`norm_mul`, `norm_zpow`, `zpow_sub₀`, `zpow_neg`, `div_zpow`, `mul_zpow`, `zpow_add₀`,
`zpow_le_zpow_right_of_le_one₀`, `div_lt_one`, `div_pos`, `inv_pos`; project:
`norm_coeff_charCoeff_upOp_le` (Halo.lean:146), `HaloRing.lean:670–697` (`hkey` pattern).
#### Sources
[LWX, (3.18.1), p. 23; (4.2.1), p. 30]; decomposition S3.  Source: 1 line ⇒ est. 40 LOC.
#### Generality decision
Any `m : ℤ` (negative included — the `HaloInt` coefficient bound covers it); `h1` is unused
here and kept only for the uniform `HYP` shape — `omit` it if the linter objects.

### [S4] (3.18.1), the case `m > λ(n)`
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:70 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_coeff_mul_zpow_le_of_gt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : (lwxLambda p (Fintype.card ι) n : ℤ) < m) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ ≤ ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * ‖T₀‖ := by sorry
```
#### Proof sketch
1. `‖b‖ ≤ 1` (`PadicInt.norm_le_one`), so `‖term‖ ≤ ‖T₀‖^m` (`norm_mul`, `hψ`, `norm_zpow`, `mul_le_of_le_one_left`).
2. `‖T₀‖^m ≤ ‖T₀‖^(λ+1)` (`zpow_le_zpow_right_of_le_one₀`, `λ + 1 ≤ m`), and `‖T₀‖^(λ+1) = ‖T₀‖^λ * ‖T₀‖`
   (`zpow_add_one₀`, `zpow_natCast`).
#### Mathlib lemmas needed
`PadicInt.norm_le_one`, `zpow_le_zpow_right_of_le_one₀`, `zpow_add_one₀`, `zpow_natCast`, `mul_le_of_le_one_left`.
#### Sources
[LWX, (3.18.1)]; decomposition S4.  est. 20 LOC.
#### Generality decision
As S3 (`h0`, `hp2` unused — keep uniform, `omit` if linted).

### [S5] The diagonal term: unit and non-unit cases
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:78, :87 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma (two)
#### Statement
```lean
theorem norm_coeff_mul_zpow_of_isUnit (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (n : ℕ)
    (hu : IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖ψ ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) *
        T₀ ^ (lwxLambda p (Fintype.card ι) n : ℤ)‖ =
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by sorry

theorem norm_coeff_mul_zpow_le_of_not_isUnit (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (n : ℕ)
    (hu : ¬ IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖ψ ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) *
        T₀ ^ (lwxLambda p (Fintype.card ι) n : ℤ)‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * (p : ℝ)⁻¹ := by sorry
```
#### Proof sketch
1. Unit: `PadicInt.isUnit_iff.1 hu : ‖b‖ = 1`; `norm_mul, hψ, norm_zpow, one_mul, zpow_natCast`.
2. Non-unit: `‖b‖ < 1` (`PadicInt.isUnit_iff` + `PadicInt.norm_le_one` + `lt_of_le_of_ne`), then
   `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one b (-1)`: `‖b‖ ≤ p^(−1) ↔ ‖b‖ < p^0 = 1` — so
   `‖b‖ ≤ p⁻¹`; multiply by `‖T₀‖^λ` (`mul_comm`).
#### Mathlib lemmas needed
`PadicInt.isUnit_iff`, `PadicInt.norm_le_one`, `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`,
`zpow_neg_one`, `zpow_zero`, `norm_mul`, `norm_zpow`, `zpow_natCast`.
#### Sources
[LWX, p. 23] "equality holding if and only if m = λ(n) and bn,λ(n) is a p-adic unit"; decomposition S5.  est. 25 LOC.
#### Generality decision
No annulus hypotheses (none needed); `T₀` explicit.

### [S6] Off-diagonal terms are strictly small
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:97 | **Depends on**: S3, S4
- **Parallel**: after S3, S4 | **Type**: lemma
#### Statement
```lean
theorem norm_coeff_mul_zpow_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : m ≠ lwxLambda p (Fintype.card ι) n) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ < ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by sorry
```
#### Proof sketch
`rcases lt_or_gt_of_ne hm`; S3 then `mul_lt_of_lt_one_right (pow_pos …) (div_lt_one … |>.2 h0)`;
S4 then `mul_lt_of_lt_one_right _ h1`.
#### Mathlib lemmas needed
`lt_or_gt_of_ne`, `mul_lt_of_lt_one_right`, `pow_pos`, `div_lt_one`, `inv_pos`.
#### Sources
[LWX, p. 23] "with the second equality holding if and only if m = λ(n)".  est. 15 LOC.
#### Generality decision
As S3.

### [CL-S1] /cleanup on PhD/LWX/Sharpness.lean (cadence)
- **Status**: done (finished 2026-09-05T13:55Z, inline) | **Depends on**: S1, S2, S3 | **Blocks**: S4–S9 (cadence; S4/S5 may be
  worked in parallel with S1–S3 and re-linted here) | **Type**: cleanup

### [S7] Cor 3.18, the equality clause
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:107 | **Depends on**: S2, S5, S6, CL-S1
- **Parallel**: with S8 | **Type**: theorem
#### Statement
```lean
theorem norm_specCharSeries_coeff_eq_of_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ)
    (hu : IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by sorry
```
#### Proof sketch
1. `rw [specCharSeries, PowerSeries.coeff_mk, HaloInt.specialize]` — a `tsum` over `ℤ` of
   `ψ (b m) * T₀^m`.
2. `Tendsto … cofinite (𝓝 0)` from `(HaloInt.summable_specialize ψ hψ h0 h1 _).tendsto_cofinite_zero`.
3. `TateFredholm.norm_tsum_eq_of_forall_lt` with `i₀ = λ`, `B = ‖T₀‖^λ`: `hi₀` = S5 (unit),
   `hlt` = S6.
#### Mathlib lemmas needed
`PowerSeries.coeff_mk`, `Summable.tendsto_cofinite_zero`; project: `HaloInt.specialize`,
`HaloInt.summable_specialize`, S2, S5, S6.
#### Sources
[LWX, Cor 3.18] (⇐); decomposition S7.  est. 20 LOC.
#### Generality decision
Mirrors `norm_specCharSeries_coeff_le`'s signature exactly.

### [S8] Cor 3.18, the margin
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:117 | **Depends on**: S3, S4, S5, CL-S1
- **Parallel**: with S7 | **Type**: theorem
#### Statement
```lean
theorem norm_specCharSeries_coeff_le_of_not_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ)
    (hu : ¬ IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * max ‖T₀‖ ((p : ℝ)⁻¹ / ‖T₀‖) := by sorry
```
#### Proof sketch
1. As S7 steps 1–2, then `(TateFredholm.norm_tsum_le_iSup htend).trans (ciSup_le fun m => ?_)`
   (this is exactly `HaloRing.lean:660–669`'s shape).
2. `rcases lt_trichotomy m λ`: `m < λ` — S3 then `mul_le_mul_of_nonneg_left (le_max_right _ _)`;
   `m = λ` — S5 (non-unit) then `p⁻¹ ≤ p⁻¹/‖T₀‖` (`le_div_self`/`div_le_iff₀` with `‖T₀‖ ≤ 1`) and
   `le_max_right`; `m > λ` — S4 then `le_max_left`.
#### Mathlib lemmas needed
`ciSup_le`, `lt_trichotomy`, `le_max_left`, `le_max_right`, `mul_le_mul_of_nonneg_left`,
`le_div_iff₀`/`div_le_iff₀`; project: `norm_tsum_le_iSup`, S3, S4, S5, `HaloRing.lean:660` pattern.
#### Sources
[LWX, Cor 3.18] "Moreover, if bn,λ(n) ∉ Z×p , then v(cn(T)) ≥ λ(n)v(T) + min{v(T), 1−v(T)}".  est. 40 LOC.
#### Generality decision
Multiplicative form; the additive `min` reading is V8.

### [S9] Cor 3.18, the equality criterion (assembly)
- **Status**: done (finished 2026-09-05T13:50Z) | **File**: PhD/LWX/Sharpness.lean:127 | **Depends on**: S7, S8
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem norm_specCharSeries_coeff_eq_iff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n ↔
      IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) := by sorry
```
#### Proof sketch
`⟨fun h => by_contra fun hu => (S8 hu).trans_lt (mul_lt_of_lt_one_right (pow_pos …) (max_lt h1 (div_lt_one … |>.2 h0))) |>.ne h, S7⟩`.
#### Mathlib lemmas needed
`max_lt`, `mul_lt_of_lt_one_right`, `div_lt_one`, `by_contra`.
#### Sources
[LWX, Cor 3.18] statement.  est. 10 LOC.
#### Generality decision
As S7.
- **Progress (S1–S9, CL-S1/2/3)**: 2026-09-05T13:50Z all nine proven in two compile cycles.
  S1: `Metric.tendsto_nhds` at `B/2` + `Filter.eventually_cofinite` finite exceptional set,
  `Finset.exists_max_image` on it, bound `M = max (B/2) ‖f i₀‖ < B`; empty-`ι` case via
  `tsum_empty`; `norm_tsum_le_iSup` + `ciSup_le`. (`Set.mem_setOf_eq` is deprecated → use
  `Set.mem_ofPred_eq`.) S2: `Summable.tsum_eq_add_tsum_ite`, `B = 0` edge case forces the
  `ite` family to vanish; otherwise `Tendsto.congr'` with the singleton-cofinite `EventuallyEq`,
  S1 on the rest, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` + `max_eq_left`.
  S3: the `(pT₀)^(m−L) ≤ (pT₀)^(−1)` trick (`zpow_le_zpow_right₀` with `1 < p‖T₀‖`), then
  `mul_zpow`/`zpow_neg_one` and `zpow_add₀` to peel `‖T₀‖^L` — no `hkey` rearrangement needed.
  S4: `PadicInt.norm_le_one` + `zpow_le_zpow_right_of_le_one₀` + `zpow_add_one₀`. S5:
  `PadicInt.isUnit_iff`; non-unit via `norm_le_pow_iff_norm_lt_pow_add_one b (-1)`.
  S6: `mul_lt_of_lt_one_right`. S7: `norm_tsum_eq_of_forall_lt` with
  `(summable_specialize …).tendsto_cofinite_zero`. S8: `norm_tsum_le_iSup` + `ciSup_le` +
  `lt_trichotomy` (the `m = λ` branch: `subst`, `p⁻¹ ≤ p⁻¹/‖T₀‖` via `le_div_iff₀`).
  S9: contrapositive with `max_lt`. Unused `h1`/`hp2` in S3/S4 renamed `_h1`/`_hp2`;
  `omit [IsUltrametricDist K] [CompleteSpace K] in` on the five per-term lemmas. Cleanup inline:
  title de-skeletoned, one wide line wrapped, lambdas already `↦`; `lake build PhD.LWX.Sharpness`
  clean, `runLinter` clean, six headline decls on standard axioms.

### [CL-S2] /cleanup on PhD/LWX/Sharpness.lean (cadence)
- **Status**: done (finished 2026-09-05T13:55Z, inline) | **Depends on**: S4, S5, S6 | **Type**: cleanup
### [CL-S3] /cleanup on PhD/LWX/Sharpness.lean (final)
- **Status**: done (finished 2026-09-05T13:55Z, inline) | **Depends on**: S7, S8, S9 | **Type**: cleanup

---

## Tranche U — `PhD/LWX/UpperPolygon.lean` (pure `ℕ`/`ℤ` combinatorics; all `Parallel: yes`)

### [U1] Block sums
- **Status**: done (finished 2026-09-05T13:55Z) | **File**: PhD/LWX/UpperPolygon.lean:37 | **Depends on**: none | **Type**: lemma
#### Statement
```lean
theorem sum_range_mul_div (t m : ℕ) (ht : 0 < t) (f : ℕ → ℕ) :
    ∑ i ∈ range (m * t), f (i / t) = t * ∑ j ∈ range m, f j := by sorry
```
#### Proof sketch
Induction on `m`: `(m+1)*t = m*t + t`, `Finset.sum_range_add` (`∑_{i<a+b} g i = ∑_{i<a} g i + ∑_{i<b} g (a+i)`);
for `i < t`, `(m*t + i)/t = m` (`Nat.mul_add_div ht`, `Nat.div_eq_of_lt`), so the second sum is
`t • f m` (`Finset.sum_const`, `card_range`); `Finset.sum_range_succ`, `mul_add`.
#### Mathlib lemmas needed
`Finset.sum_range_add`, `Finset.sum_range_succ`, `Finset.sum_const`, `Finset.card_range`,
`Nat.mul_add_div`, `Nat.div_eq_of_lt`, `smul_eq_mul`, `mul_add`.
#### Sources
[LWX, (3.23.1), p. 25]: `∑_{n<(k+1)qt}⌊n/t⌋ = t∑_{n<(k+1)q} n`.  est. 25 LOC.
#### Generality decision
Any `f : ℕ → ℕ` (used with `id` and with `j ↦ (p−1) − 2j`-type summands cast later).

### [U2] Floor shifts
- **Status**: done (finished 2026-09-05T13:55Z) | **File**: PhD/LWX/UpperPolygon.lean:42, :47 | **Depends on**: none | **Type**: lemma (two)
#### Statement
```lean
theorem touchX_add_div (p t k i : ℕ) (ht : 0 < t) :
    (touchX p t k + i) / t = k * p + i / t := by sorry

theorem touchX_add_div_mul (p t k i : ℕ) (hpt : 0 < p * t) (hi : i < p * t) :
    (touchX p t k + i) / (p * t) = k := by sorry
```
#### Proof sketch
`touchX` unfolds to `k * (p * t)`; rewrite as `i + (k*p) * t` / `i + k * (p*t)` (`mul_assoc`, `add_comm`),
then `Nat.add_mul_div_left`/`Nat.add_mul_div_right` and `Nat.div_eq_of_lt hi` (second lemma).
#### Mathlib lemmas needed
`Nat.add_mul_div_left`, `Nat.add_mul_div_right`, `Nat.div_eq_of_lt`, `mul_assoc`, `mul_comm`, `add_comm`.
#### Sources
Block decomposition in [LWX, Lemma 4.1 proof].  est. 15 LOC.
#### Generality decision
No `i < pt` needed for the first (exact identity).

### [U3] (3.23.1): `λ(n_k) = k²p(p−1)t/2`
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:52 | **Depends on**: U1 | **Type**: lemma
#### Statement
```lean
theorem two_mul_lwxLambda_touchX (p t k : ℕ) :
    2 * lwxLambda p t (touchX p t k) = k ^ 2 * p * (p - 1) * t := by sorry
```
#### Proof sketch
1. Handle `t = 0` (both sides `0`: `touchX = 0`, `range 0`) and `p = 0` (`touchX = 0`; RHS `0`)
   separately; assume `0 < t`, `0 < p`.
2. `lwxLambda` = `∑ (i/t − i/(p*t))` = `∑ i/t − ∑ i/(p*t)` (`Finset.sum_tsub_distrib`, since
   `i/(p*t) ≤ i/t` by `Nat.div_le_div_left`).
3. `∑_{i<k*(p*t)} i/t = t * ∑_{j<kp} j` (U1 with `m = k*p`, `f = id`, after `k*(p*t) = (k*p)*t`);
   `∑_{i<k*(p*t)} i/(p*t) = (p*t) * ∑_{j<k} j` (U1 with block `p*t`).
4. `Finset.sum_range_id_mul_two`: `(∑_{j<n} j) * 2 = n*(n−1)`; then `2λ = t·kp(kp−1) − pt·k(k−1)
   = k p t (kp − 1 − k + 1) = k²p(p−1)t` — cast to `ℤ` (`push_cast`, `Nat.cast_sub` with the
   order facts) and `ring`/`nlinarith`, or stay in `ℕ` with `Nat.sub` lemmas.
#### Mathlib lemmas needed
`Finset.sum_tsub_distrib`, `Nat.div_le_div_left`, `Finset.sum_range_id_mul_two`, `Nat.cast_sub`,
`push_cast`, `ring`; project: `lwxLambda`, U1.
#### Sources
[LWX, (3.23.1), p. 25] (7 source lines) and [p. 29] "λ(nk+1) = (k+1)²p(p−1)t/2".  est. 45 LOC.
#### Generality decision
No hypotheses (edge cases hold; see decomposition U3).

### [CL-U1] /cleanup on PhD/LWX/UpperPolygon.lean (cadence)
- **Status**: done (finished 2026-09-05T15:15Z, inline) | **Depends on**: U1, U2, U3 | **Type**: cleanup

### [U4] The upper polygon is linear on blocks
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:64 | **Depends on**: U2, CL-U1 | **Type**: lemma
#### Statement
```lean
theorem lwxUpperTwice_touchX_add (p t k x : ℕ) (hx : x ≤ p * t) :
    lwxUpperTwice p t (touchX p t k + x) =
      lwxUpperTwice p t (touchX p t k) + x * ((2 * k + 1) * (p - 1)) := by sorry
```
#### Proof sketch
`lwxUpperTwice`, `Finset.sum_range_add`; for `i < x ≤ p*t`, `(touchX + i)/(p*t) = k` (U2; if
`p*t = 0` then `x = 0` and both sides agree trivially); `Finset.sum_const`, `card_range`, `smul_eq_mul`.
#### Mathlib lemmas needed
`Finset.sum_range_add`, `Finset.sum_congr`, `Finset.sum_const`, `Finset.card_range`, `Nat.pos_of_ne_zero`.
#### Sources
[LWX, p. 29] "the restriction of the upper bound polygon on [nk,nk+1] is a linear function with slope (k+1/2)(p−1)v(T)".  est. 20 LOC.
#### Generality decision
`x ≤ p*t` (closed block, used with `x = p*t` in U5 and `x = n % (pt)` in U9/U10).

### [U5] The upper polygon passes through the touching vertices
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:70 | **Depends on**: U3, U4 | **Type**: lemma
#### Statement
```lean
theorem lwxUpperTwice_touchX (p t k : ℕ) :
    lwxUpperTwice p t (touchX p t k) = 2 * lwxLambda p t (touchX p t k) := by sorry
```
#### Proof sketch
Induction on `k`: `touchX (k+1) = touchX k + p*t`; U4 with `x = p*t` gives
`lwxUpperTwice (n_{k+1}) = lwxUpperTwice n_k + pt(2k+1)(p−1)`; U3 at `k` and `k+1` gives
`2λ(n_{k+1}) − 2λ(n_k) = ((k+1)² − k²)p(p−1)t = (2k+1)p(p−1)t`; `ring`/`omega` after casting.
#### Mathlib lemmas needed
`Nat.succ_mul`, `ring`, `Nat.cast` lemmas; project: U3, U4.
#### Sources
[LWX, p. 29] "the lower bound polygon and the upper bound polygon touch at the vertices (nk,λ(nk)v(T))".  est. 25 LOC.
#### Generality decision
None needed.

### [U6] The block difference as a signed sum
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:77 | **Depends on**: U2, U4, U5 | **Type**: lemma
#### Statement
```lean
theorem lwxUpperTwice_sub_two_mul_lwxLambda_eq (p t k x : ℕ) (ht : 0 < t) (hx : x ≤ p * t) :
    (lwxUpperTwice p t (touchX p t k + x) : ℤ) - 2 * lwxLambda p t (touchX p t k + x) =
      ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by sorry
```
#### Proof sketch
1. U4 for the upper side; `lwxLambda`/`Finset.sum_range_add` for the lower side:
   `λ(n_k + x) = λ(n_k) + ∑_{i<x} ((n_k+i)/t − (n_k+i)/(pt))`.
2. U2: `(n_k+i)/t = kp + i/t`, `(n_k+i)/(pt) = k` (`i < x ≤ pt`; handle `p = 0` where `pt = 0`
   forces `x = 0`), so each lower increment is `k(p−1) + i/t` (in `ℤ`, `push_cast` with `1 ≤ p`
   when `p ≥ 1`; for `p = 0`, `x = 0`).
3. U5 kills the `n_k` terms; `Finset.sum_sub_distrib`, `Finset.sum_const`, `ring_nf`:
   `(2k+1)(p−1) − 2(k(p−1) + i/t) = (p−1) − 2(i/t)`.
#### Mathlib lemmas needed
`Finset.sum_range_add`, `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_const`, `push_cast`,
`Nat.cast_sub`, `Nat.cast_div`? (avoid: keep `i / t` as a `ℕ` cast), `ring`; project: U2, U4, U5, `lwxLambda`.
#### Sources
[LWX, p. 29] "by looking at the incremental diﬀerences of slopes built from the vertex (nk,λ(nk)v(T)), ∑_{i=nk}^{n−1}((k+½)(p−1) − (⌊i/t⌋ − ⌊i/pt⌋))v(T)" (3 source lines).  est. 50 LOC.
#### Generality decision
`ℤ`-valued to keep the signed terms honest.

### [CL-U2] /cleanup on PhD/LWX/UpperPolygon.lean (cadence)
- **Status**: done (finished 2026-09-05T15:15Z, inline) | **Depends on**: U4, U5, U6 | **Type**: cleanup

### [U7] The signed block sum is nonnegative
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:83 | **Depends on**: U1, CL-U2 | **Type**: lemma
#### Statement
```lean
theorem sum_block_nonneg (p t x : ℕ) (ht : 0 < t) (hx : x ≤ p * t) :
    0 ≤ ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by sorry
```
#### Proof sketch
1. The terms are `≥ 0` for `i < (p+1)t/2`-ish and `≤ 0` after; the partial sums first increase
   then decrease, and the full sum over `x = pt` is `0`.  Cleanest route: show the partial sum is
   `≥` the full sum `∑_{i<pt}` (the removed terms `i ∈ [x, pt)` are `≤ 0` when `x ≥ h·t` with
   `h = ⌈(p−1)/2⌉`… ) — simpler: split by whether `x ≤ (p−1)/2·t` (all terms `≥ 0`:
   `Finset.sum_nonneg`, since `i/t ≤ (p−1)/2` gives `2(i/t) ≤ p − 1`) or not (then
   `∑_{i<x} = ∑_{i<pt} − ∑_{i∈[x,pt)}` with every removed term `≤ 0` because `i/t ≥ (p−1)/2`…
   careful at parity: terms with `2(i/t) = p−1` vanish).
2. Full sum: `∑_{i<pt}((p−1) − 2(i/t)) = pt(p−1) − 2t·∑_{j<p} j = pt(p−1) − t·p(p−1) = 0`
   (U1 for `∑_{i<pt} i/t = t∑_{j<p} j`, `Finset.sum_range_id_mul_two`).
#### Mathlib lemmas needed
`Finset.sum_nonneg`, `Finset.sum_range_add_sum_Ico`/`Finset.sum_Ico_eq_sub`, `Finset.sum_nonpos`,
`Finset.sum_range_id_mul_two`, `Nat.div_le_iff_le_mul_add_pred`/`Nat.le_div_iff_mul_le`, `omega`; project: U1.
#### Sources
[LWX, p. 29] the unimodal shape ("slope (k(p−1)+a)v(T) on [nk+at, nk+(a+1)t]" vs the upper slope).  est. 50 LOC.
#### Generality decision
No parity needed (holds for all `p`); `hx` needed.

### [U8] The signed block sum is at most `(p²−1)t/4`
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:90 | **Depends on**: U1, CL-U2 | **Type**: lemma
#### Statement
```lean
theorem four_mul_sum_block_le (p t x : ℕ) (hodd : Odd p) (ht : 0 < t) (hx : x ≤ p * t) :
    4 * ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤ ((p ^ 2 - 1) * t : ℕ) := by sorry
```
#### Proof sketch
1. Write `p = 2h + 1` (`hodd`).  The partial sum over `range x` is `≤` the sum over the indices with
   nonnegative terms, i.e. `≤ ∑_{i<(h+1)t}((p−1) − 2(i/t))` (`Finset.sum_le_sum_of_subset_of_nonneg`
   for `x ≤ (h+1)t`, and for `x > (h+1)t` drop the nonpositive tail: `Finset.sum_range_add` +
   `Finset.sum_nonpos`).
2. That head sum is `t·∑_{j<h+1}(2h − 2j) = 2t·∑_{j≤h}(h − j) = 2t·h(h+1)/2 = t·h(h+1)`
   (U1 with `f j = 2h − 2j` — as `ℕ` since `j ≤ h`; `Finset.sum_range_id_mul_two`/`Finset.sum_range_reflect`).
3. `4·t·h(h+1) = t·(2h+1)²−1 = (p²−1)t` (`ring` after `p = 2h+1`).
#### Mathlib lemmas needed
`Odd` destructuring, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.sum_nonpos`, `Finset.sum_range_add`,
`Finset.sum_range_reflect`, `Finset.sum_range_id_mul_two`, `Nat.cast_sub`, `ring`; project: U1.
#### Sources
[LWX, Lemma 4.1 proof, p. 29] "the maximal vertical diﬀerence over [nk,nk+1] is achieved when a = (p−1)/2 … = tv(T)∑_{j=0}^{(p−1)/2−1}((p−1)/2 − j) = (p²−1)tv(T)/8" (8 source lines).  est. 60 LOC.
#### Generality decision
`Odd p` (the source's `p > 2` for a prime); false for `p = 2` (decomposition U8 attack 1).

### [U9] Lower ≤ upper
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:96 | **Depends on**: U6, U7 | **Type**: theorem
#### Statement
```lean
theorem two_mul_lwxLambda_le_lwxUpperTwice (p t n : ℕ) (hp : 0 < p) (ht : 0 < t) :
    2 * lwxLambda p t n ≤ lwxUpperTwice p t n := by sorry
```
#### Proof sketch
`n = touchX p t (n / (p*t)) + n % (p*t)` (`Nat.div_add_mod`, `touchX` unfolded, `mul_comm`);
`n % (p*t) ≤ p*t` (`Nat.mod_lt`); U6 gives the difference as the signed sum, U7 makes it `≥ 0`;
cast back (`Int.toNat`-free: `sub_nonneg`, `Nat.cast_le`).
#### Mathlib lemmas needed
`Nat.div_add_mod`, `Nat.mod_lt`, `sub_nonneg`, `Nat.cast_le`, `exact_mod_cast`.
#### Sources
[LWX, Lemma 4.1] (the difference is a nonnegative "vertical difference").  est. 20 LOC.
#### Generality decision
`0 < p` (false for `p = 0`, decomposition U9).

### [CL-U3] /cleanup on PhD/LWX/UpperPolygon.lean (cadence)
- **Status**: done (finished 2026-09-05T15:15Z, inline) | **Depends on**: U7, U8, U9 | **Type**: cleanup

### [U10] LWX Lemma 4.1
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:102 | **Depends on**: U6, U8, U9, CL-U3 | **Type**: theorem
#### Statement
```lean
theorem lwxUpperTwice_sub_two_mul_lwxLambda_le (p t n : ℕ) (hodd : Odd p) (ht : 0 < t) :
    4 * (lwxUpperTwice p t n - 2 * lwxLambda p t n) ≤ (p ^ 2 - 1) * t := by sorry
```
#### Proof sketch
As U9 with U8 in place of U7; the `ℕ` subtraction is exact by U9 (`Nat.cast_sub`), so the
`ℤ` inequality of U8 transfers (`exact_mod_cast`).
#### Mathlib lemmas needed
`Nat.div_add_mod`, `Nat.mod_lt`, `Nat.cast_sub`, `exact_mod_cast`, `Odd.pos`.
#### Sources
[LWX, Lemma 4.1, p. 29] "The maximal vertical diﬀerence between the lower bound polygon and the upper bound polygon is (p²−1)tv(T)/8 for p > 2".  est. 20 LOC.
#### Generality decision
`Odd p`; `≤` form (attainment not consumed).

### [U11] The band increment
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:110 | **Depends on**: U2 | **Type**: lemma
#### Statement
```lean
theorem div_sub_div_eq_of_mem_band (p t k n : ℕ) (hp : 0 < p) (ht : 0 < t)
    (h1 : touchX p t k ≤ n + t) (h2 : n < touchX p t k + t) :
    n / t - n / (p * t) = k * (p - 1) := by sorry
```
#### Proof sketch
Case `n < touchX k` (then `k ≥ 1`, write `n = touchX (k−1) + (pt − t) + r`… simpler: establish
`n / t = k*p − 1` and `n / (p*t) = k − 1` via `Nat.div_eq_of_lt_le` (`(kp−1)t ≤ n < kp·t`,
`(k−1)pt ≤ n < kpt`)); case `touchX k ≤ n`: `n/t = kp`, `n/(pt) = k` (U2 with `i = n − touchX k < t`);
then `omega` (`k*(p−1) = k*p − k`, `Nat.mul_sub_one`).
#### Mathlib lemmas needed
`Nat.div_eq_of_lt_le`, `Nat.le_div_iff_mul_le`, `Nat.div_lt_iff_lt_mul`, `Nat.mul_sub_one`, `omega`; project: U2.
#### Sources
[LWX, p. 25] "⌊nk/t⌋−⌊nk/pt⌋ = kq−kq/p−1 = kφ(q)".  est. 35 LOC.
#### Generality decision
`0 < p`, `0 < t`.

### [U12] The band identities
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:116, :121 | **Depends on**: U11 | **Type**: lemma (two)
#### Statement
```lean
theorem lwxLambda_touchX_add (p t k i : ℕ) (hp : 0 < p) (ht : 0 < t) (hi : i ≤ t) :
    lwxLambda p t (touchX p t k + i) = lwxLambda p t (touchX p t k) + k * (p - 1) * i := by sorry

theorem lwxLambda_touchX_sub (p t k i : ℕ) (hp : 0 < p) (ht : 0 < t) (hi : i ≤ t)
    (hik : i ≤ touchX p t k) :
    lwxLambda p t (touchX p t k - i) + k * (p - 1) * i = lwxLambda p t (touchX p t k) := by sorry
```
#### Proof sketch
Induction on `i` with `lwxLambda_succ` (Halo.lean:44) and U11 at `n = touchX k + i` (`i < t`) /
`n = touchX k − i − 1` (in the band since `i + 1 ≤ t`); `omega` for the bookkeeping.
#### Mathlib lemmas needed
`Nat.succ_le`, `Nat.sub_succ`, `omega`; project: `lwxLambda_succ`, U11.
#### Sources
[LWX, p. 25] "λ(nk+1−i) ≥ λ(nk+1) − (k+1)φ(q)i with equality if and only if i ∈ [−t,t]" (equality half).  est. 40 LOC.
#### Generality decision
`i ≤ t` closed band.

### [CL-U4] /cleanup on PhD/LWX/UpperPolygon.lean (cadence)
- **Status**: done (finished 2026-09-05T15:15Z, inline) | **Depends on**: U10, U11, U12 | **Type**: cleanup

### [U13] Strict excess beyond the band
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:128, :134 | **Depends on**: U12, CL-U4 | **Type**: lemma (two)
#### Statement
```lean
theorem lwxLambda_touchX_add_ge (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) (hi : t ≤ i) :
    lwxLambda p t (touchX p t k) + k * (p - 1) * i + (i - t) ≤
      lwxLambda p t (touchX p t k + i) := by sorry

theorem lwxLambda_touchX_sub_ge (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) (hi : t ≤ i)
    (hik : i ≤ touchX p t k) :
    lwxLambda p t (touchX p t k) + (i - t) ≤
      lwxLambda p t (touchX p t k - i) + k * (p - 1) * i := by sorry
```
#### Proof sketch
1. Right: at `n = touchX k + t`, `n/t − n/(pt) = kp + 1 − k = k(p−1) + 1` (U2); the increment
   `n ↦ n/t − n/(pt)` is monotone (`monotone_sub_div p` composed with `n ↦ n/t`, via
   `Nat.div_div_eq_div_mul` — the argument of `monotone_lwxSlopes`, Halo.lean:186–196), so every
   step from `touchX k + t` on adds `≥ k(p−1) + 1`; induction on `i − t` from U12 at `i = t`.
2. Left: at `n = touchX k − t − 1` (exists since `i ≥ t + 1 ≤ touchX k`), `n/t = kp − 2`,
   `n/(pt) = k − 1` (needs `p ≥ 2`: `n ≥ (k−1)pt + (p−2)t`), increment `k(p−1) − 1`; monotone
   below; induction downward from U12 at `i = t`.
#### Mathlib lemmas needed
`Nat.div_div_eq_div_mul`, `Nat.div_le_div_right`, `Nat.le_induction`, `omega`; project:
`monotone_sub_div`, `lwxLambda_succ`, U2, U12.
#### Sources
[LWX, p. 25] the "only if" of the band sentence, quantified by its proof mechanism (monotone increments).  est. 70 LOC.
#### Generality decision
`1 < p` (false at `p = 1`, decomposition U13 attack 1).

### [U14] The band sentence verbatim (iff)
- **Status**: done (finished 2026-09-05T15:10Z) | **File**: PhD/LWX/UpperPolygon.lean:141 | **Depends on**: U12, U13 | **Type**: lemma
#### Statement
```lean
theorem lwxLambda_touchX_add_eq_iff (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) :
    lwxLambda p t (touchX p t k + i) = lwxLambda p t (touchX p t k) + k * (p - 1) * i ↔
      i ≤ t := by sorry
```
#### Proof sketch
`⟨fun h => by_contra fun hi => by have := U13 (le_of_lt (not_le.1 hi)); omega, U12⟩`.
#### Mathlib lemmas needed
`not_le`, `omega`.
#### Sources
[LWX, p. 25] "with equality if and only if i ∈ [−t,t]" (right half).  est. 10 LOC.
#### Generality decision
As U13.
- **Progress (U1–U14, CL-U1..5)**: 2026-09-05T15:10Z whole tranche proven (four compile
  cycles). Recurring trap: `omega` (and `push_cast`/`exact_mod_cast`) push `↑(i / t)` to the
  ℤ-division `↑i / ↑t`, losing nonnegativity and mismatching atoms — always `generalize i / t = d`
  (NOT `set`, which omega sees through) before `omega`/`linarith`, and cast sums with
  `congrArg Nat.cast` + `push_cast`/`simp only [Nat.cast_sum]` on one side only. U3 via
  `Finset.sum_tsub_distrib` + `sum_range_mul_div` twice + `Finset.sum_range_id_mul_two` and
  `zify [hk, hp, hkp]` + `linear_combination`. U6: `lwxUpperTwice_touchX_add` + `touchX_add_div`
  with `Nat.mul_sub_one` and `nsmul_eq_mul` (ℤ-valued sums). U7/U8: threshold
  `q = (p+1)/2` resp. `h + 1` (`p = 2h+1`), `Finset.sum_nonneg`/`sum_nonpos` on the two sides
  with `Finset.sum_range_add_sum_Ico`, head sum via `sum_range_mul_div` + `Finset.sum_range_reflect`;
  `Finset.range_mono` (not `range_subset`) for the subset step. U9/U10: `n = touchX (n/(pt)) +
  n % (pt)` (`Nat.div_add_mod` after `Nat.mul_comm`), `zify [hle, hp2]`. U11: `Nat.div_eq_of_lt_le`
  both floors, atoms generalized. U13: `monotone_sub_div` must be applied with an explicit
  `have h : … := monotone_sub_div p …` type (else beta-redexes block `rw`), `Nat.le_induction`
  via `induction i, hi using Nat.le_induction`. Cleanup inline: title de-skeletoned, no wide
  lines, no `=>` lambdas; `lake build` clean (2538 jobs), 6 headline decls standard axioms,
  `runLinter` clean.

### [CL-U5] /cleanup on PhD/LWX/UpperPolygon.lean (final)
- **Status**: done (finished 2026-09-05T15:15Z, inline) | **Depends on**: U13, U14 | **Type**: cleanup

---

## Tranche V — `PhD/LWX/Vertices.lean`

### [V1] `k = 0` is free
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:51, :78 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (two)
#### Statement
```lean
theorem isUnitCoeff_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsUnitCoeff D ω 0 := by sorry

theorem hasUnitBand_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    HasUnitBand D ω 0 := by sorry
```
#### Proof sketch
`IsUnitCoeff`: `charCoeff_zero` gives `c₀ = 1`; `lwxLambda p t 0 = 0` (`Finset.sum_range_zero`);
`(1 : HaloInt p) 0 = 1` (`HaloInt.coeff_one`), `isUnit_one`.  `HasUnitBand 0`: both witnesses `n = 0`
(`touchX 0 = 0`; `0 ≤ 0 + t`, `0 ≤ 0`, `0 ≤ 0 + t`).
#### Mathlib lemmas needed
`isUnit_one`, `Finset.sum_range_zero`; project: `charCoeff_zero`, `HaloInt.coeff_one`.
#### Sources
[LWX, p. 26] "we set n−0 = 0 and n+0 the maximal index in [0,t] such that bn+0,0 is a p-adic unit".  est. 15 LOC.
#### Generality decision
None.

### [V2] `n_k^−` specification
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:83, :90 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (two)
#### Statement
```lean
theorem leftIndex_mem (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) :
    touchX p (Fintype.card ι) k ≤ leftIndex D ω k + Fintype.card ι ∧
      leftIndex D ω k ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω (leftIndex D ω k) := by sorry

theorem not_isUnitCoeff_of_lt_leftIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k n : ℕ}
    (hb : HasUnitBand D ω k) (hn : touchX p (Fintype.card ι) k ≤ n + Fintype.card ι)
    (hlt : n < leftIndex D ω k) : ¬ IsUnitCoeff D ω n := by sorry
```
#### Proof sketch
`leftIndex` is `sInf S`; `S.Nonempty` from `hb.1`; `Nat.sInf_mem` gives the three clauses.
Minimality: if `IsUnitCoeff n` with `hn` and `n ≤ touchX k` (from `n < leftIndex ≤ touchX k`)
then `n ∈ S`, so `sInf S ≤ n` (`Nat.sInf_le`), contradicting `hlt`.
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.sInf_le`, `Set.Nonempty`, `not_lt`.
#### Sources
[LWX, p. 26] "n−k+1 … is the minimal index in [nk+1−t,nk+1] … such that b … is a p-adic unit".  est. 25 LOC.
#### Generality decision
`sInf` (no decidability); the `mem` lemma bundles the three defining clauses of one membership.

### [V3] `n_k^+` specification
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:96, :104 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (two)
#### Statement
```lean
theorem rightIndex_mem (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) :
    touchX p (Fintype.card ι) k ≤ rightIndex D ω k ∧
      rightIndex D ω k ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧
      IsUnitCoeff D ω (rightIndex D ω k) := by sorry

theorem not_isUnitCoeff_of_rightIndex_lt (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k n : ℕ}
    (hb : HasUnitBand D ω k) (hn : n ≤ touchX p (Fintype.card ι) k + Fintype.card ι)
    (hlt : rightIndex D ω k < n) : ¬ IsUnitCoeff D ω n := by sorry
```
#### Proof sketch
`rightIndex = sSup S`, `S` nonempty (`hb.2`) and bounded above by `touchX k + t` (`BddAbove`);
`Nat.sSup_mem`; maximality via `le_csSup` (`hbdd`, membership) contradicting `hlt`.
#### Mathlib lemmas needed
`Nat.sSup_mem`, `le_csSup`, `BddAbove`, `Set.Nonempty`.
#### Sources
[LWX, p. 26] "(resp. maximal index in [nk+1,nk+1+t])".  est. 25 LOC.
#### Generality decision
As V2.

### [CL-V1] /cleanup on PhD/LWX/Vertices.lean (cadence)
- **Status**: done (finished 2026-09-05T15:40Z, inline — final lint/width pass deferred to the file's final cleanup) | **Depends on**: V1, V2, V3 | **Type**: cleanup

### [V4] `n_k^+ ≤ n_{k+1}^−`
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:110 | **Depends on**: V2, V3, CL-V1 | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem rightIndex_le_leftIndex_succ (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) (hb' : HasUnitBand D ω (k + 1)) :
    rightIndex D ω k ≤ leftIndex D ω (k + 1) := by sorry
```
#### Proof sketch
`rightIndex k ≤ touchX k + t` (V3) and `touchX (k+1) ≤ leftIndex (k+1) + t` (V2);
`touchX (k+1) = touchX k + p*t ≥ touchX k + 2t` (`hp.out.two_le`); `omega`.
#### Mathlib lemmas needed
`Nat.Prime.two_le`, `omega`.
#### Sources
[LWX, (3.23.3)/(3.23.4)] (degrees nonnegative).  est. 15 LOC.
#### Generality decision
Needs only `2 ≤ p`.

### [V5] `bandLine` API
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:123, :127, :132 | **Depends on**: U12 | **Parallel**: yes | **Type**: def API (three)
#### Statement
```lean
@[simp] theorem bandLine_touchX (p t k : ℕ) (vT : ℝ) :
    bandLine p t k vT (touchX p t k) = (lwxLambda p t (touchX p t k) : ℝ) * vT := by sorry

theorem bandLine_add_one (p t k : ℕ) (vT : ℝ) (x : ℤ) :
    bandLine p t k vT (x + 1) = bandLine p t k vT x + ((k * (p - 1) : ℕ) : ℝ) * vT := by sorry

theorem bandLine_eq_of_mem_band (p t k : ℕ) (hp : 0 < p) (ht : 0 < t) (vT : ℝ) {n : ℕ}
    (h1 : touchX p t k ≤ n + t) (h2 : n ≤ touchX p t k + t) :
    bandLine p t k vT n = (lwxLambda p t n : ℝ) * vT := by sorry
```
#### Proof sketch
First two: unfold, `ring`/`push_cast`.  Third: `n = touchX k + i` (`i ≤ t`) or `n = touchX k − i`
(`i ≤ t`, `i ≤ touchX k`); U12 gives `λ(n)` as `λ(n_k) ± k(p−1)i`; cast to `ℝ` (`Nat.cast_add`,
`Nat.cast_sub` with the U12 identity to avoid truncation), `ring`.
#### Mathlib lemmas needed
`push_cast`, `Nat.cast_sub`, `ring`, `Int.cast_natCast`; project: U12.
#### Sources
[LWX, p. 26] "the line segment … has slope kφ(q)v(T), and passes through the point (nk,λ(nk)v(T))".  est. 35 LOC.
#### Generality decision
`vT` arbitrary real (no positivity needed).

### [V6] Cor 3.18 in `coeffVal` form
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:142 | **Depends on**: none | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem le_coeffVal_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) n := by sorry
```
#### Proof sketch
`by_cases` coefficient `= 0` (`coeffVal_eq_top_iff`, `le_top`); else `coeffVal_of_ne_zero`,
`WithTop.coe_le_coe`, `Real.log_le_log` on `norm_specCharSeries_coeff_le`, `Real.log_pow`, `linarith`
(this is `hlog` in Halo.lean:224–231).
#### Mathlib lemmas needed
`Real.log_le_log`, `Real.log_pow`, `norm_pos_iff`, `WithTop.coe_le_coe`; project: `coeffVal_of_ne_zero`,
`coeffVal_eq_top_iff`, `norm_specCharSeries_coeff_le`.
#### Sources
[LWX, Cor 3.18] inequality.  est. 15 LOC.
#### Generality decision
As `norm_specCharSeries_coeff_le`.

### [CL-V2] /cleanup on PhD/LWX/Vertices.lean (cadence)
- **Status**: done (finished 2026-09-05T15:40Z, inline — final lint/width pass deferred to the file's final cleanup) | **Depends on**: V4, V5, V6 | **Type**: cleanup

### [V7] (3.23.2), unit case in `coeffVal` form
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:150 | **Depends on**: S7, CL-V2 | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem coeffVal_specCharSeries_of_isUnitCoeff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {n : ℕ} (hu : IsUnitCoeff D ω n) :
    coeffVal (specCharSeries D ω ψ T₀) n =
      (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
S7 gives the norm `= ‖T₀‖^λ ≠ 0`; `coeffVal_of_ne_zero`, `Real.log_pow`, `neg_mul`, `mul_comm`.
#### Mathlib lemmas needed
`Real.log_pow`, `pow_ne_zero`, `norm_ne_zero_iff`; project: S7, `coeffVal_of_ne_zero`.
#### Sources
[LWX, (3.23.2)].  est. 15 LOC.
#### Generality decision
As V6.

### [V8] The margin in `coeffVal` form
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Vertices.lean:159 | **Depends on**: S8, CL-V2 | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem le_coeffVal_specCharSeries_of_not_isUnitCoeff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {n : ℕ} (hu : ¬ IsUnitCoeff D ω n) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) +
        min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) n := by sorry
```
#### Proof sketch
Zero coefficient: `le_top`.  Else S8 and `Real.log_le_log` (norm positive), `Real.log_mul`,
`Real.log_pow`; `−log(max a b) = min(−log a, −log b)` — do `max_cases`/`le_max_iff` case split and
`Real.log_le_log_iff`; `Real.log_div`, `Real.log_inv` for `−log(p⁻¹/‖T₀‖) = log p + log‖T₀‖`; `linarith`.
#### Mathlib lemmas needed
`Real.log_mul`, `Real.log_pow`, `Real.log_div`, `Real.log_inv`, `Real.log_le_log`, `max_cases`/`min_le_iff`, `linarith`; project: S8.
#### Sources
[LWX, Cor 3.18] margin.  est. 35 LOC.
#### Generality decision
Additive form for the polygon arguments.

### [V9] Step II: the segment
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:171 | **Depends on**: NP2, V2, V3, V5, V6, V7, U13 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem height_specCharSeries_eq_bandLine (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx1 : (leftIndex D ω k : ℤ) ≤ x) (hx2 : x ≤ rightIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x =
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. Set up `hNP : IsNewtonPolygonOf (coeffVal f) NP_T` via `isNewtonPolygonOf_powerSeries` with
   `hex`/`hadm` exactly as in `isBelow_newtonPolygon_specCharSeries` (Halo.lean:219–242 — copy the
   admissibility block; consider extracting it as a private helper `isNewtonPolygonOf_specCharSeries`
   in this file, reused by V10/V11/V13) and `hx0 : NP_T.starting_point.1 = 0`
   (`newtonPolygon₀_starting_point_of_coeff_zero_eq_one (specCharSeries_coeff_zero …)`).
2. **Points above the line**: for every `n`, `bandLine n ≤ pointHeight (coeffVal f) n`: `pointHeight`
   vs `coeffVal` (`pointHeight_coe`/`pointHeight_eq_top_iff`), V6 gives `λ(n)vT ≤ coeffVal n`, and
   `bandLine n ≤ λ(n)vT`: in the band by V5 (`bandLine_eq_of_mem_band`, equality); beyond by U13
   (`λ(n) ≥ λ(n_k) ± k(p−1)i + (i − t)`, cast, `vT > 0`).
3. **Lower bound**: NP2 with `a = bandLine 0`, `b = k(p−1)vT` (`bandLine_add_one` shows
   `bandLine n = a + b n`) gives `bandLine x ≤ height x` (for `x ≥ 0`, from `hx1`).
4. **Upper bound**: `height (n_k^−) ≤ pointHeight = bandLine (n_k^−)` (V2 membership, V7, V5) and
   likewise at `n_k^+` (V3); `height_le_chord` with `x = n_k^−`, `z = n_k^+`, `y = x`; the chord
   through two points of the line is the line (`ring` on the explicit formula; handle
   `n_k^− = n_k^+` by `hx1`/`hx2` forcing `x = n_k^−`).
5. `le_antisymm`.
#### Mathlib lemmas needed
`le_antisymm`, `WithBotTop.coe_le_coe`, `Real.log_neg` (for `vT > 0`), `ring`, `div_add_div_same`;
project: NP2, `height_le_chord` (Height.lean:740), `isNewtonPolygonOf_powerSeries`,
`newtonPolygon₀_starting_point_of_coeff_zero_eq_one`, `isAdmissible_of_affine_bound`, `pointHeight_coe`,
V2, V3, V5, V6, V7, U13.
#### Sources
[LWX, p. 26] "the line segment connecting these two vertices has slope kφ(q)v(T), and passes through the point (nk,λ(nk)v(T))" (Step II, 6 source lines for this half).  est. 110 LOC.
#### Generality decision
`x : ℤ` (the polygon's height is on `ℤ`); `[Nonempty ι]` for the band lemmas.

### [CL-V3] /cleanup on PhD/LWX/Vertices.lean (cadence)
- **Status**: done (finished 2026-09-05T17:35Z, inline) | **Depends on**: V7, V8, V9 | **Type**: cleanup

### [V10] Step II: strict left of `n_k^−`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:181 | **Depends on**: NP1, V2, V5, V6, V8, U13, CL-V3 | **Parallel**: with V11 | **Type**: theorem
#### Statement
```lean
theorem bandLine_lt_height_specCharSeries_of_lt_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx0 : 0 ≤ x) (hx : x < leftIndex D ω k) :
    (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x := by sorry
```
#### Proof sketch
1. `μ := min vT (log p + log‖T₀‖) > 0` (`0 < vT < log p` from `h0 h1`, `Real.log_lt_log`,
   `Real.log_inv`); `N := leftIndex k > 0` (from `hx0`, `hx`).
2. Points: for `n < N`: `pointHeight n ≥ bandLine n + μ` — if `touchX k ≤ n + t` then `n` is a band
   non-unit (V2 minimality) and V8 + V5 give it; else `n < touchX k − t`, U13 (`i = touchX k − n > t`)
   gives `λ(n)vT ≥ bandLine n + (i − t)vT ≥ bandLine n + vT ≥ bandLine n + μ` with V6.  For `n ≥ N`:
   `≥ bandLine n` as in V9 step 2.
3. NP1 with `y₀ = bandLine 0 + μ`, `s₁ = b − μ/N`, `s₂ = b` (`hs` by `μ/N > 0`); check the point
   hypothesis: for `n ≤ N` the competitor is `bandLine n + μ(1 − n/N) ≤ bandLine n + μ`; for
   `n ≥ N` it is `bandLine n`.
4. At `k := x.toNat`: competitor `= bandLine x + μ(N − x)/N > bandLine x` (`div_pos`, `sub_pos`).
#### Mathlib lemmas needed
`Real.log_lt_log`, `Real.log_inv`, `lt_min`, `div_pos`, `sub_pos`, `min_le_left`, `Int.toNat_of_nonneg`,
`field_simp`/`ring`; project: NP1, V2, V5, V6, V8, U13, the `IsNewtonPolygonOf` setup from V9.
#### Sources
[LWX, p. 26] "the first inequality is a strict inequality if nk−t ≤ nk−i < n−k (by the minimality of n−k) and the second inequality is a strict inequality if nk−i < nk−t … the diﬀerences in all strict inequalities are at least min{v(T), 1−v(T)}".  est. 110 LOC.
#### Generality decision
Strict form only (the margin `μ(N−x)/N` is proof-internal).

### [V11] Step II: strict right of `n_k^+`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:191 | **Depends on**: NP1, V3, V5, V6, V8, U13, CL-V3 | **Parallel**: with V10 | **Type**: theorem
#### Statement
```lean
theorem bandLine_lt_height_specCharSeries_of_rightIndex_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx : (rightIndex D ω k : ℤ) < x) :
    (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x := by sorry
```
#### Proof sketch
As V10 with `N := rightIndex k`, `y₀ = bandLine 0`, `s₁ = b`, `s₂ = b + μ/(t+2)`; points `n > N`:
band non-units (V3 maximality, V8): `≥ bandLine n + μ ≥ bandLine n + μ(n−N)/(t+2)` since
`n − N ≤ t`; beyond the band (`n = touchX k + t + m`, `m ≥ 1`): U13 gives `≥ bandLine n + m vT ≥
bandLine n + m μ ≥ bandLine n + μ(n−N)/(t+2)` because `n − N ≤ m + t ≤ (t+2) m`.  Conclusion at
`x`: competitor `= bandLine x + μ(x−N)/(t+2) > bandLine x`.
#### Mathlib lemmas needed
As V10 plus `div_le_iff₀`, `Nat.cast_le`, `nlinarith`/`omega` for `n − N ≤ (t+2)m`.
#### Sources
[LWX, p. 26] "Similarly, we have the inequality v(cnk+i(T)) ≥ v(T)(λ(nk) + kφ(q)i), which becomes a strict inequality if nk+i > n+k".  est. 110 LOC.
#### Generality decision
As V10; the divisor `t + 2` is the smallest that works uniformly (decomposition V11 attack 1).

### [V12] Touching at every halo point
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:202 | **Depends on**: V9 | **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem height_specCharSeries_touchX (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        (touchX p (Fintype.card ι) k) =
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ) := by sorry
```
#### Proof sketch
V9 at `x = touchX k` (`leftIndex ≤ touchX k ≤ rightIndex` from V2/V3), then `bandLine_touchX`.
#### Mathlib lemmas needed
`Nat.cast_le`; project: V9, V2, V3, V5.
#### Sources
[LWX, p. 26/29] "passes through the point (nk,λ(nk)v(T))".  est. 10 LOC.
#### Generality decision
None.

### [CL-V4] /cleanup on PhD/LWX/Vertices.lean (cadence)
- **Status**: done (finished 2026-09-05T17:35Z, inline) | **Depends on**: V10, V11, V12 | **Type**: cleanup

### [V13] The bridge: touching at one point ⟹ `HasUnitBand`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:214 | **Depends on**: NP1, V1, V5, V6, V8, U13, CL-V4 | **Parallel**: with V14–V16 | **Type**: theorem
#### Statement
```lean
theorem hasUnitBand_of_height_eq (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ}
    (h : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        (touchX p (Fintype.card ι) k) =
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ)) :
    HasUnitBand D ω k := by sorry
```
#### Proof sketch
1. `k = 0`: V1.  `k ≥ 1`: `touchX k ≥ p*t ≥ 1`.
2. Left conjunct by contradiction: no unit in `[touchX k − t, touchX k]` ⟹ every `n ≤ touchX k` has
   `pointHeight n ≥ bandLine n + μ` (band: V8 + V5; beyond: U13 + V6), every `n > touchX k` has
   `≥ bandLine n` (V6 + U13/V5).  NP1 with `N = touchX k + 1`, `y₀ = bandLine 0 + μ`,
   `s₁ = b − μ/N`, `s₂ = b`: at `x = touchX k`, `height ≥ bandLine(touchX k) + μ/N = λ(n_k)vT + μ/N`,
   contradicting `h` (`WithBotTop.coe_lt_coe`, `bandLine_touchX`).
3. Right conjunct: no unit in `[touchX k, touchX k + t]` ⟹ `n ≥ touchX k` has `≥ bandLine n + μ`,
   `n < touchX k` has `≥ bandLine n`.  NP1 with `N = touchX k − 1`, `y₀ = bandLine 0`, `s₁ = b`,
   `s₂ = b + μ/(t+2)`: points `n ≥ touchX k = N + 1`: need `bandLine n + μ(n−N)/(t+2) ≤ pointHeight n`
   — band (`n − N ≤ t + 1 < t + 2`) by the margin; beyond (`n = touchX k + t + m`) by U13 as in V11
   (`n − N = m + t + 1 ≤ (t+2)m`).  At `x = touchX k`: `height ≥ λ(n_k)vT + μ/(t+2)` — contradiction.
#### Mathlib lemmas needed
As V10/V11; `Nat.one_le_iff_ne_zero`, `Nat.Prime.pos`, `Fintype.card_pos`.
#### Sources
[LWX, pp. 25–26] "It follows that n−k+1 ∈ [nk+1−t,nk+1] and n+k+1 ∈ [nk+1,nk+1+t]. Moreover, the equivalence (3.23.2) implies that n−k+1 (resp. n+k+1) is the minimal index … (resp. maximal index …) such that b … is a p-adic unit" (Step II, first half; 8 source lines).  est. 130 LOC.
#### Generality decision
Any halo `T₀` (the source uses `T_{χ_k}`); this is what makes `HasUnitBand` the honest hypothesis.

### [V14] Slopes on the band
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:227 | **Depends on**: V9, NP3, NP4 | **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem unitSlope_specCharSeries_eq_of_mem_band (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj1 : leftIndex D ω k ≤ j) (hj2 : j < rightIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
      ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
NP3 with `hj := V9 at j`, `hj1 := V9 at j+1` (both in `[n_k^−, n_k^+]`), `hb` from NP4 (`NP_T` is
`newtonPolygon₀OfSeq (coeffVal f)` with `hex`/`hadm` from V9's setup), then `bandLine_add_one`
(`sub_eq`), and the anchor `hx0` from V9's setup.
#### Mathlib lemmas needed
`Nat.cast_succ`, `add_sub_cancel_left`; project: NP3, NP4, V9, V5.
#### Sources
[LWX, p. 26] "the line segment connecting these two vertices has slope kφ(q)v(T)".  est. 20 LOC.
#### Generality decision
None.

### [V15] Slopes after `n_k^+` exceed `kφ(q)v(T)`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:236 | **Depends on**: V9, V11, NP3, NP4 | **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem lt_unitSlope_specCharSeries_of_rightIndex_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj : rightIndex D ω k ≤ j) :
    ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j := by sorry
```
#### Proof sketch
1. Let `N := rightIndex k`.  `height N = bandLine N` (V9).  Case `height (N+1) = ⊤`: Height.lean's
   `unitSlope_eq_top_of_height_eq_top` (line 542, public since 2026-09-05; it gives
   `unitSlope ((x − start).toNat − 1) = ⊤` from `height x = ⊤`, here `x = N + 1`) yields
   `unitSlope N = ⊤`, and `⊤ > _` (`WithBotTop` order).  Case finite `= c`: V11 at `N + 1` gives
   `c > bandLine (N+1)`; NP3 (with NP4 for `≠ ⊥`): `unitSlope N = c − bandLine N > bandLine (N+1)
   − bandLine N = b vT` (`bandLine_add_one`).
2. For `j ≥ N`: `unitSlope_mono hj` and `lt_of_lt_of_le`.
#### Mathlib lemmas needed
`lt_of_lt_of_le`, `WithBotTop.coe_lt_coe`, `WithBotTop.coe_lt_top`, `sub_lt_sub_right`; project:
NP3, NP4, V9, V11, `unitSlope_mono`, `unitSlope_eq_top_of_height_eq_top` (Height.lean:542),
`height_eq_bot_iff` (height at `N` is not `⊥`).
#### Sources
[LWX, (3.23.4)] and the `X_{(k,k+1)}` clause of Theorem 1.3.  est. 45 LOC.
#### Generality decision
Holds even if the polygon ends (`⊤`).

### [CL-V5] /cleanup on PhD/LWX/Vertices.lean (cadence)
- **Status**: done (finished 2026-09-05T17:35Z, inline) | **Depends on**: V13, V14, V15 | **Type**: cleanup

### [V16] Slopes before `n_k^−` are below `kφ(q)v(T)`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:245 | **Depends on**: V9, V10, NP3, NP4, CL-V5 | **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem unitSlope_specCharSeries_lt_of_lt_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj : j < leftIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j <
      ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. `N := leftIndex k ≥ 1`; `M := N − 1`.  `height N = bandLine N` (V9); `height M` is finite:
   `≤` the chord between `height 0 = 0` (anchor: `newtonPolygon₀_starting_point_of_coeff_zero_eq_one`,
   `height` at the starting point) and `height N` (`height_le_chord`), and `≠ ⊥` (`height_eq_bot_iff`);
   let `a := toReal`.  V10 at `M`: `a > bandLine M`.
2. NP3 (`≠ ⊥` by NP4): `unitSlope M = bandLine N − a < bandLine N − bandLine M = b vT`.
3. `j ≤ M`: `unitSlope_mono`, `lt_of_le_of_lt`.
#### Mathlib lemmas needed
`lt_of_le_of_lt`, `sub_lt_sub_left`, `WithBotTop` case analysis; project: NP3, NP4, V9, V10, `unitSlope_mono`,
`height_le_chord`, `height_eq_bot_iff`.
#### Sources
[LWX, (3.23.3)] and the `X_{(k−1,k)}` clause.  est. 50 LOC.
#### Generality decision
None.

### [CLEANUP-ALL-1] /cleanup-all on the six board files (pre-milestone)
- **Status**: done (finished 2026-09-05T17:35Z, inline) | **Depends on**: V16 and every open NP/S/U ticket | **Blocks**: V17 | **Type**: cleanup

### [V17] MILESTONE — Theorem 1.3's `X_k`: the slope-`kφ(q)` block is exactly `[n_k^−, n_k^+)`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:256 | **Depends on**: V14, V15, V16, CLEANUP-ALL-1 | **Parallel**: with V18 | **Type**: theorem (milestone)
#### Statement
```lean
theorem unitSlope_specCharSeries_eq_iff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
        ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ↔
      leftIndex D ω k ≤ j ∧ j < rightIndex D ω k := by sorry
```
#### Proof sketch
`⟨fun h => ⟨not_lt.1 fun hj => (V16 hj).ne h, not_le.1 fun hj => (V15 hj).ne' h⟩, fun ⟨h1, h2⟩ => V14 h1 h2⟩`.
#### Mathlib lemmas needed
`not_lt`, `not_le`, `ne_of_lt`, `ne_of_gt`.
#### Sources
[LWX, Theorem 1.3, p. 3] "for each point x ∈ XI with I = [n,n] … v(ap(x)) ∈ φ(q)v(Twt(x))·I" and [(3.23.3)–(3.23.4), p. 26].  est. 15 LOC.
#### Generality decision
Per `k`; the multiplicity `n_k^+ − n_k^−` is `T`-free (that is the theorem's content).

### [V18] MILESTONE — Theorem 1.3's `X_{(k,k+1)}`
- **Status**: done (finished 2026-09-05T17:30Z) | **File**: PhD/LWX/Vertices.lean:266 | **Depends on**: V4, V15, V16, CLEANUP-ALL-1 | **Parallel**: with V17 | **Type**: theorem (milestone)
#### Statement
```lean
theorem unitSlope_specCharSeries_mem_Ioo (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k)
    (hb' : HasUnitBand D ω (k + 1)) {j : ℕ} (hj1 : rightIndex D ω k ≤ j)
    (hj2 : j < leftIndex D ω (k + 1)) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j ∈
      Set.Ioo ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ)
        (((((k + 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
`⟨V15 hb hj1, V16 hb' hj2⟩` (`Set.mem_Ioo`).
#### Mathlib lemmas needed
`Set.mem_Ioo`.
#### Sources
[LWX, Theorem 1.3] `I = (n, n+1)`; multiplicity `n_{k+1}^− − n_k^+` (V4 makes the interval well formed).  est. 5 LOC.
#### Generality decision
As V17.
- **Progress (V9–V18, CL-V3..6, CLEANUP-ALL-1)**: 2026-09-05T17:30Z. New public helpers added to
  Vertices.lean (all consumed ≥ 2×): `bandLine_le_lwxLambda_mul`, `bandLine_add_le_lwxLambda_mul_of_le/_of_ge`
  (quantitative excess beyond the band), `le_pointHeight_of_le_coeffVal`, `pointHeight_eq_of_coeffVal_eq`,
  `exists_coeffVal_specCharSeries_ne_top`, `isAdmissible_coeffVal_specCharSeries`,
  `isNewtonPolygonOf_specCharSeries`, `specCharSeries_starting_point_fst`, `unitSlope_specCharSeries_ne_bot`,
  `exists_coe_of_ne_bot_of_ne_top`, `bandLine_eq_add_mul`, `bandLine_le_pointHeight`,
  `bandLine_add_min_le_pointHeight`, `bandLine_add_le_pointHeight_of_ge/_of_le`. V9 = `line_le_height`
  + `height_le_chord` with the affine identity of the chord (degenerate `n⁻ = n⁺` case by `simp`).
  V10/V11/V13 = `twoSlope_le_height` with the planned competitors (`μ/N`, `μ/(t+2)`); three-product
  chains need explicit `mul_le_mul_of_nonneg_*` steps (nlinarith alone fails). V14–V16 =
  `unitSlope_eq_of_height_eq` + `unitSlope_eq_top_of_height_eq_top` (now public) for the ended-polygon
  arm + `unitSlope_mono`. Traps: `set` variables desynchronise from later-produced hypotheses
  (write `Fintype.card ι`/`-Real.log ‖T₀‖` explicitly); helper calls need `(k := k)` pinned; `ℕ`
  casts of `bandLine`'s `((x : ℤ) : ℝ)` need `Int.cast_natCast`. Cleanup inline: title de-skeletoned,
  30 over-wide lines auto-wrapped (codepoint-measured), no `=>` lambdas; `lake build` clean
  (2540 jobs), V9/V13/V17/V18 on standard axioms; CLEANUP-ALL-1 = `runLinter` clean on all five
  finished modules.

### [CL-V6] /cleanup on PhD/LWX/Vertices.lean (final)
- **Status**: done (finished 2026-09-05T17:35Z, inline) | **Depends on**: V17, V18 | **Type**: cleanup

---

## Tranche C — `PhD/LWX/Claim.lean`

### [C1] Units only at `m ≥ λ(l)`
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Claim.lean:52 | **Depends on**: none | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem lwxLambda_le_of_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    {l : ℕ} {m : ℤ} (hu : IsUnit ((charCoeff (D.op ω) l) m)) :
    (lwxLambda p (Fintype.card ι) l : ℤ) ≤ m := by sorry
```
#### Proof sketch
`by_contra`; `m < λ` ⟹ `‖b‖ ≤ p^(m−λ) ≤ p⁻¹ < 1` (`norm_coeff_charCoeff_upOp_le`,
`zpow_le_zpow_right_of_le_one₀`? no — `p > 1`: `zpow_le_zpow_right₀` with negative exponent `≤ −1`,
`zpow_neg_one`, `inv_lt_one`), contradicting `PadicInt.isUnit_iff.1 hu : ‖b‖ = 1`.
#### Mathlib lemmas needed
`PadicInt.isUnit_iff`, `zpow_le_zpow_right₀`, `zpow_neg_one`, `inv_lt_one_iff₀`, `Nat.one_lt_cast`; project: `norm_coeff_charCoeff_upOp_le`.
#### Sources
[LWX, Cor 3.18 proof] "v(bn,m) ≥ max{λ(n)−m, 0}".  est. 20 LOC.
#### Generality decision
`m : ℤ`.

### [C2] `unitIndex` API
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Claim.lean:58, :64, :69, :74 | **Depends on**: C1 | **Parallel**: yes | **Type**: def API (four)
#### Statement
```lean
theorem isUnit_unitIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l : ℕ}
    (h : ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) :
    IsUnit ((charCoeff (D.op ω) l) (unitIndex D ω l : ℤ)) := by sorry

theorem not_isUnit_of_lt_unitIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l m : ℕ}
    (hm : m < unitIndex D ω l) : ¬ IsUnit ((charCoeff (D.op ω) l) (m : ℤ)) := by sorry

theorem unitIndex_le (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l m : ℕ}
    (hu : IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) : unitIndex D ω l ≤ m := by sorry

theorem lwxLambda_le_unitIndex (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    {l : ℕ} (h : ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) :
    lwxLambda p (Fintype.card ι) l ≤ unitIndex D ω l := by sorry
```
#### Proof sketch
`Nat.sInf_mem h`; `fun hu => (Nat.sInf_le hu).not_lt hm`; `Nat.sInf_le hu`; C1 on `isUnit_unitIndex`
(`Int.ofNat_le`/`exact_mod_cast`).
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.sInf_le`, `Set.Nonempty`, `Nat.cast_le`.
#### Sources
[LWX, p. 30] "Let m(l) be the minimal one satisfying this property" / "Hence bl,m ∈ pZp for those m".  est. 25 LOC.
#### Generality decision
`sInf`; the existence hypothesis is explicit where needed.

### [C3] The radius condition, additively
- **Status**: done (finished 2026-09-05T15:40Z) | **File**: PhD/LWX/Claim.lean:85 | **Depends on**: none | **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem kappa_lt (hp2 : p ≠ 2) {T₀ : K} (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) :
    (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) * (-Real.log ‖T₀‖) <
      8 * (Real.log p + Real.log ‖T₀‖) := by sorry
```
#### Proof sketch
`‖T₀‖ > 0` from `hκ` (RHS positive ⟹ base nonzero; `pow_pos`/`pos_of_pow_pos`... or `lt_of_lt_of_le`
with `inv_pos`); `Real.log_lt_log (by positivity) hκ`, `Real.log_pow` on both sides, `Real.log_inv`;
`push_cast`, `linarith`.
#### Mathlib lemmas needed
`Real.log_lt_log`, `Real.log_pow`, `Real.log_inv`, `Nat.cast_add`, `Nat.cast_mul`, `linarith`, `positivity`.
#### Sources
[LWX, p. 30, (4.2.1)] "λ(l)v(T) − v(T) + 1 > λ(l)v(T) + (p²−1)tv(T)/8" ⟺ `v(T) < 8/((p²−1)t+8)`.  est. 20 LOC.
#### Generality decision
`h1` only for the sign of `log‖T₀‖` if needed; `hp2` unused (uniformity) — `omit` if linted.

### [CL-C1] /cleanup on PhD/LWX/Claim.lean (cadence)
- **Status**: done (finished 2026-09-05T15:40Z, inline — final lint/width pass deferred to the file's final cleanup) | **Depends on**: C1, C2, C3 | **Type**: cleanup

### [C4] The Claim, analytic core
- **Status**: done (finished 2026-09-05T16:20Z) | **File**: PhD/LWX/Claim.lean:95 | **Depends on**: S1, S2, S3, S4, U10, C1, C3, CL-C1 | **Parallel**: with C6 | **Type**: theorem
#### Statement
```lean
theorem exists_isUnit_and_coeffVal_eq (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (hbelow : coeffVal (specCharSeries D ω ψ T₀) l <
      (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ)) :
    ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ)) ∧
      coeffVal (specCharSeries D ω ψ T₀) l = (((m : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
Work with `C := ‖c_l(T₀)‖ > 0` (from `hbelow`: coefficient nonzero, `coeffVal_of_ne_zero`) and
`vT > 0`.  Write `Λ⁺ := lwxUpperTwice l / 2` and `gap := (p²−1)t/8`; U10 gives `Λ⁺ ≤ λ(l) + gap`;
C3 gives `gap·vT < log p − vT`.
1. **(4.2.2)** For `m < λ(l)`: S3 ⟹ `−log‖term_m‖ ≥ λvT + (log p − vT) > λvT + gap·vT ≥ Λ⁺vT > −log C`,
   so `‖term_m‖ < C`.
2. **Existence of a dominant index**: `¬ ∀ m ≥ λ, ‖term_m‖ < C` — else all terms `< C` and S1
   (`Tendsto` from `HaloInt.summable_specialize`) gives `C < C`.  So `∃ m ≥ λ, C ≤ ‖term_m‖`;
   `m ≥ λ ≥ 0` so take `m : ℕ` and let `m₀ := Nat.find` of `{m | λ ≤ m ∧ C ≤ ‖term_m‖}`.
3. **`b_{l,m₀}` is a unit**: `‖b‖ = ‖term_{m₀}‖/‖T₀‖^{m₀} ≥ C/‖T₀‖^{λ}` (`‖T₀‖^{m₀} ≤ ‖T₀‖^λ`), and
   `C/‖T₀‖^λ > ‖T₀‖^{gap} … > p⁻¹` (from `hbelow` + U10 + C3 in log form: `v(b) ≤ v(c_l) − λvT <
   gap·vT < log p`), hence `‖b‖ > p⁻¹`, so `‖b‖ = 1` (`PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`,
   `PadicInt.isUnit_iff`).
4. **All other terms are strictly smaller than `‖term_{m₀}‖ = ‖T₀‖^{m₀}`** (S5-type unit identity):
   `m < λ` by step 1 (`< C ≤ ‖term_{m₀}‖`); `λ ≤ m < m₀` by `Nat.find_min'` (`‖term_m‖ < C`);
   `m > m₀` by S4-type bound `‖term_m‖ ≤ ‖T₀‖^m < ‖T₀‖^{m₀}` (`zpow_lt_zpow_right_of_lt_one₀`).
5. S2 ⟹ `C = ‖T₀‖^{m₀}`; `coeffVal_of_ne_zero`, `Real.log_pow` ⟹ the second conjunct; `⟨m₀, unit, _⟩`.
#### Mathlib lemmas needed
`Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `PadicInt.isUnit_iff`, `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`,
`zpow_lt_zpow_right_of_lt_one₀`, `Real.log_lt_log`, `Real.log_pow`, `Real.log_inv`, `div_le_iff₀`, `linarith`;
project: S1, S2, S3, S4, U10, C1, C3, `coeffVal_of_ne_zero`, `HaloInt.summable_specialize`, `norm_coeff_charCoeff_upOp_le`.
#### Sources
[LWX, p. 30, lwx.txt:2261–2289] (4.2.1)–(4.2.4), part 1 of the Claim's proof (25 source lines).  est. 130 LOC.
#### Generality decision
Shared-witness existential (documented exception in decomposition C4); `hκ` explicit.

### [C5] Strictly below at one point ⟹ `IsBelowUpper`
- **Status**: done (finished 2026-09-05T16:20Z) | **File**: PhD/LWX/Claim.lean:107 | **Depends on**: C4, C2 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem isBelowUpper_of_coeffVal_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (hbelow : coeffVal (specCharSeries D ω ψ T₀) l <
      (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ)) :
    IsBelowUpper D ω l := by sorry
```
#### Proof sketch
`obtain ⟨m, hu, hv⟩ := C4 …`; `⟨⟨m, hu⟩, _⟩`: `unitIndex ≤ m` (C2) and from `hv ▸ hbelow`,
`m·vT < (Λ⁺₂/2)·vT` ⟹ `m < Λ⁺₂/2` (`mul_lt_mul_right` with `vT > 0`), so `2m < Λ⁺₂` (`Nat.cast`,
`exact_mod_cast` after `lt_div_iff`).
#### Mathlib lemmas needed
`WithTop.coe_lt_coe`, `mul_lt_mul_right`, `lt_div_iff₀`, `Nat.cast_lt`, `exact_mod_cast`.
#### Sources
[LWX, p. 30–31] "Since the point (l, m(l)v(T0)) lies strictly below the upper bound polygon for T0".  est. 25 LOC.
#### Generality decision
As C4.

### [C6] The Claim: `T`-independence
- **Status**: done (finished 2026-09-05T16:20Z) | **File**: PhD/LWX/Claim.lean:118 | **Depends on**: S2, S3, S4, S5, C2, C3, U10, CL-C1 | **Parallel**: with C4 | **Type**: theorem
#### Statement
```lean
theorem coeffVal_specCharSeries_eq_unitIndex_mul (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (h : IsBelowUpper D ω l) :
    coeffVal (specCharSeries D ω ψ T₀) l =
      (((unitIndex D ω l : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
`m₀ := unitIndex l`, unit by C2; `λ ≤ m₀` (C2); `2m₀ < Λ⁺₂` (`h.2`), U10: `Λ⁺₂/2 ≤ λ + gap`, C3.
Show every `m ≠ m₀` has `‖term_m‖ < ‖T₀‖^{m₀}` and apply S2 (with S5-unit for the `m₀` term):
- `m < λ`: S3, then `λvT + (log p − vT) > λvT + gap·vT ≥ (Λ⁺₂/2)vT > m₀ vT` (log form).
- `λ ≤ m < m₀`: non-unit (C2), so `‖b‖ ≤ p⁻¹` and `‖term‖ ≤ p⁻¹‖T₀‖^m ≤ p⁻¹‖T₀‖^λ`; in log form
  `≥ log p + λvT > gap·vT + λvT ≥ (Λ⁺₂/2)vT > m₀vT`.
- `m > m₀`: `‖term‖ ≤ ‖T₀‖^m < ‖T₀‖^{m₀}`.
Then `coeffVal_of_ne_zero`, `Real.log_pow`.
#### Mathlib lemmas needed
`PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`, `PadicInt.isUnit_iff`, `zpow_lt_zpow_right_of_lt_one₀`,
`Real.log_pow`, `Real.log_lt_log`, `linarith`, `lt_trichotomy`; project: S2, S3, S4, S5, C2, C3, U10,
`coeffVal_of_ne_zero`, `HaloInt.summable_specialize`.
#### Sources
[LWX, pp. 30–31, lwx.txt:2290–2302] part 2 of the Claim's proof (12 source lines).  est. 100 LOC.
#### Generality decision
Hypothesis `IsBelowUpper` (not `hbelow` at some `T₀`) so that the statement is `T`-free.

### [CL-C2] /cleanup on PhD/LWX/Claim.lean (cadence)
- **Status**: done (finished 2026-09-05T16:25Z, inline) | **Depends on**: C4, C5, C6 | **Type**: cleanup

### [C7] The Claim's contrapositive
- **Status**: done (finished 2026-09-05T16:20Z) | **File**: PhD/LWX/Claim.lean:129 | **Depends on**: C5, CL-C2 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem le_coeffVal_specCharSeries_of_not_isBelowUpper (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (h : ¬ IsBelowUpper D ω l) :
    (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) l := by sorry
```
#### Proof sketch
`not_lt.1 fun hlt => h (C5 … hlt)`.
#### Mathlib lemmas needed
`not_lt`.
#### Sources
[LWX, p. 30] "Granting the claim … the convex hull of points …" (the dichotomy).  est. 5 LOC.
#### Generality decision
As C6.
- **Progress (C1–C7, CL-C1..3)**: 2026-09-05T16:20Z. C4 (the analytic core, ~110 LOC) and C6
  (~95 LOC) both compiled on the second cycle; the only failure was the `hgap` cast bookkeeping:
  after `set L := lwxLambda …`, facts produced later still mention `lwxLambda …` — `rw [← hL] at`
  them — and `push_cast at h ⊢` must be applied to BOTH sides so `↑((p²−1)·t)` splits identically.
  Structure of C4 exactly as sketched: `hstar` (below-upper + Lemma 4.1 + `kappa_lt` ⟹
  `−log‖c‖ < L·vT + log p + log‖T₀‖`, via `nlinarith`), `hsmall` (S3 in log form), `hex` by
  contradiction with S1, `Nat.find`, unit via the non-unit bound `‖b‖ ≤ p⁻¹` (inline, not the
  diagonal S5 lemma, since `m₀ ≠ λ`), `hothers` by `lt_trichotomy` (`Nat.find_min`,
  `zpow_lt_zpow_right_of_lt_one₀`), S2, `coeffVal_of_ne_zero` + `Real.log_pow`. C6 is the same
  skeleton with `unitIndex` and `not_isUnit_of_lt_unitIndex`. `Int.eq_ofNat_of_zero_le` lifts the
  ℤ-index to ℕ. `set term : ℤ → K := …` needs `rw [hterm]; simp only` before `norm_mul`.
  C2's `Nat.sInf_le`/`Nat.sInf_mem` need `(s := {m | …})`; `.not_lt` does not resolve on `Nat.le`
  (use `absurd h (not_lt.2 …)`). Cleanup inline: title, one docstring wrapped, `runLinter` clean,
  `lake build` clean (2539 jobs), C4/C6/C7 on standard axioms.

### [CL-C3] /cleanup on PhD/LWX/Claim.lean (final)
- **Status**: done (finished 2026-09-05T16:25Z, inline) | **Depends on**: C7 | **Type**: cleanup

---

## Tranche P — `PhD/LWX/SlopeRatios.lean`

### [P1] The shape polygon exists and is anchored at the origin
- **Status**: done (finished 2026-09-05T18:40Z) | **File**: PhD/LWX/SlopeRatios.lean:54, :59 | **Depends on**: C2 | **Parallel**: yes | **Type**: def API (two)
#### Statement
```lean
theorem isNewtonPolygonOf_shapePolygon (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsNewtonPolygonOf (shapeVal D ω) (shapePolygon D ω) := by sorry

theorem shapePolygon_starting_point (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    (shapePolygon D ω).starting_point = (0, 0) := by sorry
```
#### Proof sketch
1. `shapeVal 0 = λ(0) = 0`: `IsBelowUpper D ω 0` is false — `unitIndex 0 = 0` (`b_{0,0} = 1` unit,
   `Nat.sInf` of a set containing `0`), `lwxUpperTwice 0 = 0` (`range 0`), so `2·0 < 0` fails; and
   `p*t ∣ 0`.  Hence `∃ i, shapeVal i ≠ ⊤`.
2. `IsAdmissible`: `isAdmissible_of_affine_bound (m := 0) (b := 0)` — every finite value is a
   nonnegative real (`Nat.cast_nonneg`).
3. `isNewtonPolygonOf_newtonPolygon₀OfSeq`.
4. Starting point: from `start_mem`/`start_le` of (3): the first finite index is `0` (`start_le`
   contrapositive at `k = 0`) with value `shapeVal 0 = 0`; `Prod.ext`.
#### Mathlib lemmas needed
`Nat.sInf_eq_zero`/`Nat.sInf_le`, `dvd_zero`, `Nat.cast_nonneg`, `Prod.ext`, `if_pos`/`if_neg`;
project: `isNewtonPolygonOf_newtonPolygon₀OfSeq`, `isAdmissible_of_affine_bound`, `charCoeff_zero`,
`HaloInt.coeff_one`, C2.
#### Sources
[LWX, p. 30] "the Newton polygon … is the convex hull of points {(nk,λ(nk)v(T))}k≥0 ∐ {(li,m(li)v(T)}i∈I".  est. 45 LOC.
#### Generality decision
Unconditional (no `HasUnitBand`, no annulus).

### [P2] The shape polygon lies below the upper polygon, and is finite
- **Status**: done (finished 2026-09-05T18:40Z) | **File**: PhD/LWX/SlopeRatios.lean:65, :72 | **Depends on**: P1, U4, U5 | **Parallel**: yes | **Type**: lemma (two)
#### Statement
```lean
theorem height_shapePolygon_le (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) :
    (shapePolygon D ω).height n ≤
      (((lwxUpperTwice p (Fintype.card ι) n : ℝ) / 2 : ℝ) : WithBotTop ℝ) := by sorry

theorem height_shapePolygon_ne_top (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) : (shapePolygon D ω).height n ≠ ⊤ := by sorry
```
#### Proof sketch
1. `k := n / (p*t)`, `n ∈ [touchX k, touchX (k+1)]`.  `height (touchX k) ≤ pointHeight = λ(touchX k)`
   (`P1.height_le`, `shapeVal` at a multiple of `pt`; `IsBelowUpper (touchX k)` is false since
   `unitIndex ≥ λ = Λ⁺₂/2` there — C2 + U5 — so the second branch fires), likewise at `touchX (k+1)`.
2. `height_le_chord` (`x = touchX k`, `z = touchX (k+1)`, `y = n`) with `a = λ(touchX k)`,
   `c = λ(touchX (k+1))`; the chord equals `lwxUpperTwice n / 2` by U4 (linear on the block) and
   U5 (`lwxUpperTwice (touchX k) = 2λ(touchX k)`): `field_simp`, `ring`.
3. Finiteness: `ne_top_of_le_ne_top WithBotTop.coe_ne_top (height_shapePolygon_le …)`.
#### Mathlib lemmas needed
`Nat.div_add_mod`, `Nat.mod_lt`, `ne_top_of_le_ne_top`, `field_simp`, `ring`, `Nat.cast_sub`; project:
P1, `height_le_chord`, `pointHeight_coe`, U4, U5, C2, `lwxLambda_le_unitIndex`.
#### Sources
[LWX, p. 29] "always lies below the polygon with vertices (nk,λ(nk)v(T))" (for the shape's hull).  est. 70 LOC.
#### Generality decision
`[Nonempty ι]` for `pt > 0`.

### [P3] The two hulls agree
- **Status**: done (finished 2026-09-05T18:40Z) | **File**: PhD/LWX/SlopeRatios.lean:82 | **Depends on**: NP4, NP5, P1, P2, V12, C6, C7 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem height_specCharSeries_eq_smul_shape (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hband : ∀ k, HasUnitBand D ω k) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height n =
      (((-Real.log ‖T₀‖) * NewtonPolygon.toReal ((shapePolygon D ω).height n) : ℝ) :
        WithBotTop ℝ) := by sorry
```
#### Proof sketch
Let `S := shapePolygon D ω` (anchor `(0,0)`, P1; all heights finite, P2), `hs n := toReal (S.height n)`,
`σ j := toReal (S.unitSlope j)` (monotone, NP5).  Let `NP := NP_T` with `hNP` (as V9 step 1), anchor
`0`; all `NP` heights finite: for `n ≤ touchX k`, `height (touchX k) ≠ ⊤` (V12 with `hband k`) and
`height_eq_top_mono` contrapositive; `τ j := toReal (NP.unitSlope j)` monotone (NP5).
By `height_eq_heightFun` + `heightFun` unfolded (`Algebra.algebraMap_self_apply`): `S.height n =
∑_{i<n} σ i` and `NP.height n = ∑_{i<n} τ i`.
- **(≥)**: `Q := ofSlopes (fun j => vT * σ j) (monotone: `vT > 0`) 0`; `height_ofSlopes`:
  `Q.height n = vT * hs n`.  `Q ≤ data`: for each `n`, `vT·hs n ≤ pointHeight (coeffVal f) n`:
  if `IsBelowUpper n`: `hs n ≤ unitIndex n` (`P1.height_le` at `n`, `shapeVal` first branch) and
  `pointHeight = unitIndex·vT` (C6); else `pointHeight ≥ (Λ⁺₂ n/2)·vT` (C7) `≥ vT·hs n` (P2);
  (`coeffVal = ⊤` gives `le_top`).  So `hNP.isGreatest Q rfl-anchor hQ : Q.IsBelow NP`, i.e.
  `vT·hs n ≤ NP.height n`.
- **(≤)**: `Q' := ofSlopes (fun j => τ j / vT) (monotone) 0`; `Q'.height n = (∑ τ)/vT = NP.height n / vT`.
  `Q' ≤ shapeVal` points: `IsBelowUpper n`: `NP.height n ≤ pointHeight = unitIndex·vT` (C6,
  `hNP.height_le`) so `/vT ≤ unitIndex`; `pt ∣ n` (`n = touchX k`): V12 gives `NP.height n = λ(n)vT`;
  `⊤`: `le_top`.  So `(P1).isGreatest Q' … : Q'.IsBelow S`, i.e. `NP.height n / vT ≤ hs n`.
- Combine: `le_antisymm` after `div_le_iff₀ (vT > 0)`; coerce with `WithBotTop.coe_le_coe`.
#### Mathlib lemmas needed
`Finset.mul_sum`, `Finset.sum_div`, `div_le_iff₀`, `le_div_iff₀`, `mul_le_mul_left`, `le_antisymm`,
`Monotone.const_mul`/`Monotone.div_const`, `Nat.dvd_iff_mod_eq_zero`, `exists_nat_eq`/`Nat.div_mul_cancel`;
project: NP4, NP5, P1, P2, V12, C6, C7, `height_eq_heightFun`, `heightFun`, `ofSlopes`,
`height_ofSlopes`, `ofSlopes_starting_point`,
`IsNewtonPolygonOf.isGreatest`, `IsNewtonPolygonOf.height_le`, `isBelow_iff_height`, `height_eq_top_mono`,
`isNewtonPolygonOf_powerSeries`, `newtonPolygon₀_starting_point_of_coeff_zero_eq_one`, `pointHeight_coe`.
#### Sources
[LWX, p. 30] "Granting the claim, we conclude that … the Newton polygon of ∑ cn(T)Xn is the convex hull of points {(nk,λ(nk)v(T))}k≥0 ∐ {(li,m(li)v(T)}i∈I" (8 source lines).  est. 160 LOC.
#### Generality decision
`hband` for all `k` (finiteness and every vertex height); stated with `toReal` of the shape height
(finite by P2) rather than a scaled polygon (no scaling API).

### [CL-P1] /cleanup on PhD/LWX/SlopeRatios.lean (cadence)
- **Status**: done (finished 2026-09-05T18:50Z, inline) | **Depends on**: P1, P2, P3 | **Type**: cleanup

### [CLEANUP-ALL-2] /cleanup-all on the six board files (pre-milestone)
- **Status**: done (finished 2026-09-05T18:50Z, inline) | **Depends on**: CL-P1, CL-V6, CL-C3 and every other open ticket | **Blocks**: P4 | **Type**: cleanup

### [P4] MILESTONE — Theorem 1.5, first half, at the polygon level
- **Status**: done (finished 2026-09-05T18:40Z) | **File**: PhD/LWX/SlopeRatios.lean:95 | **Depends on**: P3, NP3, NP4, P2, CLEANUP-ALL-2 | **Parallel**: no | **Type**: theorem (milestone)
#### Statement
```lean
theorem unitSlope_specCharSeries_eq_slopeRatio (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hband : ∀ k, HasUnitBand D ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
      (((-Real.log ‖T₀‖) * slopeRatio D ω j : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. NP3 on `NP_T` (`≠ ⊥` by NP4) with heights `vT·hs j`, `vT·hs (j+1)` (P3): `unitSlope j = vT(hs (j+1) − hs j)`.
2. NP3 on `S` (`≠ ⊥` by NP4 with P1's `hex`/`hadm`; heights finite by P2, anchor by P1):
   `S.unitSlope j = hs (j+1) − hs j`; `slopeRatio` is its `toReal` (`toReal_coe`).  `mul_sub`.
#### Mathlib lemmas needed
`mul_sub`, `WithBotTop.coe_inj`; project: NP3, NP4, P1, P2, P3, `NewtonPolygon.toReal_coe`.
#### Sources
[LWX, Theorem 1.5, p. 4] "(1.5.1) v(ap(y)) = φ(q)v(Twt(y))αi(ω)"; [§4.2, p. 30] "It is then clear that the ratios to v(T) of the slopes of this polygon are independent of T".  est. 25 LOC.
#### Generality decision
`slopeRatio` is `T`-free by construction; the annulus is the source's `λ = p^{−8/((p²−1)t+8)}`.
- **Progress (P1–P4, CL-P1/2, CLEANUP-ALL-2, CLEANUP-FINAL)**: 2026-09-05T18:40Z. New shape API:
  `not_isBelowUpper_zero`, `shapeVal_zero`, `not_isBelowUpper_touchX`, `shapeVal_touchX`,
  `shapeVal_of_isBelowUpper`, `exists_shapeVal_ne_top`, `isAdmissible_shapeVal`,
  `unitSlope_shapePolygon_ne_bot`, `height_shapePolygon_eq_toReal`, `toReal_height_shapePolygon`.
  P1: `isNewtonPolygonOf_newtonPolygon₀OfSeq` + `start_mem`/`starting_point_fst_le` for the anchor
  (`Prod.ext`). P2: `height_le_chord` over the block after `obtain ⟨k, x, hx, rfl⟩` (substituting
  `n = n_k + x` avoids `%`-casts leaking through ℤ; pass `(y := ((n_k + x : ℕ) : ℤ))` explicitly —
  binop elaboration otherwise pushes the ℕ→ℤ cast to the summands), chord identity via
  `lwxUpperTwice_touchX_add`/`lwxUpperTwice_touchX`, `field_simp` needs `↑p ≠ 0` and `↑t ≠ 0`
  separately (not the product). P3: exactly the two `isGreatest` applications of the plan with
  `ofSlopes` of `vT • σ` (`Monotone.const_mul`) and `τ / vT` (`Monotone.div_const`), finiteness of
  the specialized heights from `height_specCharSeries_touchX` + `height_eq_top_mono`. P4:
  `unitSlope_eq_of_height_eq` on both polygons. `lake build PhD.LWX.SlopeRatios` clean (2542 jobs);
  `#print axioms` on `unitSlope_specCharSeries_eq_iff`, `_mem_Ioo`, `height_specCharSeries_eq_smul_shape`,
  `unitSlope_specCharSeries_eq_slopeRatio`: `propext`/`Classical.choice`/`Quot.sound` only;
  `runLinter` clean on all six modules; zero `sorry` in all six files; TateFredholm README and
  plan.md updated (CLEANUP-FINAL).

### [CL-P2] /cleanup on PhD/LWX/SlopeRatios.lean (final)
- **Status**: done (finished 2026-09-05T18:50Z, inline) | **Depends on**: P4 | **Type**: cleanup

### [CLEANUP-FINAL] /cleanup-all on the whole board
- **Status**: done (finished 2026-09-05T18:50Z, inline) | **Depends on**: every other ticket | **Type**: cleanup
- **Description**: `lake exe runLinter` on all six modules; `#print axioms` on V17, V18, P4
  (expect `propext`/`Classical.choice`/`Quot.sound` only); update this board's Summary and
  `PhD/TateFredholm/README.md`'s "Notes for future work" (the two ultrametric `tsum` lemmas are
  upstream candidates); record in `plan.md` whether `slopeRatio → ∞` is worth a follow-up.
