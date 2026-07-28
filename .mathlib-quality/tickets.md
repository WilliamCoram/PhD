# Ticket Board — Martin's Weierstrass division & preparation (full generality)

Project: prove [Mar16, §1.3] (Prop 1.27 + Cor 1.28) over an arbitrary ultrametric
complete normed commutative ring at an arbitrary radius. All new code in `PhD/Martin/`.
The Lean skeleton exists and compiles (sorries only); every proof ticket is
"fill the sorry at the given declaration". Source locators refer to
`.mathlib-quality/references/martin-sec1.3.txt`; full quotes and attack logs in
`.mathlib-quality/decomposition.md` (leaf ids L1–L24 cited per ticket).

## Summary
- Total: 31 tickets (20 proof/def + 8 per-file cleanups + 2 cleanup-all + 1 final)
- Open: 0 | In Progress: 0 | Done: 31 (board completed 2026-07-28)
- Milestones: T015 (Proposition 1.27), T018 (Corollary 1.28)
- Parallel capacity: 3 workers at start (T001 ∥ T004 ∥ T010), 2–3 sustained

## Build/verify
`lake build PhD.Martin.WeierstrassPrep` (builds the whole chain).
`lean_diagnostic_messages` per touched file; no new axioms (check
`#print axioms` on T015/T018 endpoints at milestone completion).

---

### [T001] IsNormMulUnit core API (Def 1.20 + Lemma 1.21 + bridge)
- **Status**: done (2026-07-28; 6/6 decls, lake env lean clean; deviations: eq_inv_of_mul_eq_one_right not _left; coe_inv_units golfed via inv_inv) | **File**: PhD/Martin/NormMulUnit.lean | **Depends on**: none | **Parallel**: yes | **Type**: def + API
- **Leaves**: L1, L2, L4. Skeleton: NormMulUnit.lean:25–57, :65.

#### Statement (fill these sorries)
```lean
lemma IsNormMulUnit.mul {u v : A} (hu : IsNormMulUnit u) (hv : IsNormMulUnit v) :
    IsNormMulUnit (u * v)
lemma isNormMulUnit_one [NormOneClass A] : IsNormMulUnit (1 : A)
lemma IsNormMulUnit.norm_coe_inv_units [NormOneClass A] {u : Aˣ}
    (hu : IsNormMulUnit (u : A)) : ‖((u⁻¹ : Aˣ) : A)‖ = ‖(u : A)‖⁻¹
lemma isNormMulUnit_of_norm_coe_inv_units {u : Aˣ}
    (hn : ‖((u⁻¹ : Aˣ) : A)‖ = ‖(u : A)‖⁻¹) : IsNormMulUnit (u : A)
lemma IsNormMulUnit.coe_inv_units [NormOneClass A] {u : Aˣ}
    (hu : IsNormMulUnit (u : A)) : IsNormMulUnit ((u⁻¹ : Aˣ) : A)
lemma IsUnit.isNormMulUnit [NormMulClass A] {u : A} (hu : IsUnit u) : IsNormMulUnit u
```

#### Proof sketch
1. `mul`: `⟨hu.isUnit.mul hv.isUnit, fun a => by rw [mul_assoc, hu.norm_mul, hv.norm_mul, mul_assoc]⟩`.
2. `one`: `one_mul`, `norm_one`.
3. `norm_coe_inv_units` (source :51–52): from `hu.norm_mul ↑u⁻¹`, `Units.mul_inv`,
   `norm_one`: `1 = ‖u‖ * ‖↑u⁻¹‖`; conclude `eq_inv_of_mul_eq_one_left`-style
   (real-number algebra; `‖u‖ ≠ 0` since `‖u‖ * ‖↑u⁻¹‖ = 1`).
4. converse (source :53–56): if `‖(u:A)‖ = 0`: for all `a`, `‖u*a‖ ≤ ‖u‖‖a‖ = 0`,
   both sides 0. Else: `‖a‖ = ‖↑u⁻¹ * (u * a)‖ ≤ ‖↑u⁻¹‖ * ‖u*a‖ = ‖u‖⁻¹ * ‖u*a‖`
   gives `≥`; `norm_mul_le` gives `≤`.
5. `coe_inv_units`: apply 3 then 4 with `u⁻¹` (`inv_inv`, `norm_coe_inv_units` gives
   the needed norm identity for `u⁻¹`).
6. `IsUnit.isNormMulUnit`: `⟨hu, fun a => norm_mul _ _⟩` (NormMulClass `norm_mul` is
   an equality).

#### Mathlib lemmas needed
`Units.mul_inv`, `Units.inv_mul`, `norm_one`, `norm_mul_le` (NormedRing axiom),
`norm_mul` (NormMulClass), `inv_inv`, `eq_inv_of_mul_eq_one_left` (or `CancelDenoms`
by hand). All standard; verify locally with `exact?` as needed.

#### Sources
[Mar16] §1.3: Def 1.20 (txt:47–49), Lemma 1.21 + proof (txt:50–56). LOC: source proves
1.21 in 6 lines → expect ~35 LOC total for the six lemmas.

#### Generality decision
`[NormedRing A]` (no commutativity — left multiplicativity suffices downstream);
`NormOneClass` only on the three lemmas that genuinely use `‖1‖ = 1` (see
decomposition L2 attack log: the converse direction provably doesn't need it).

---

### [T002] Remark 1.22: `1 + small` is a multiplicative unit
- **Status**: done (2026-07-28; direct isosceles route — norm_add_eq_max twice + isUnit_one_sub_of_norm_lt_one; file now 0 sorries, std axioms) | **File**: PhD/Martin/NormMulUnit.lean | **Depends on**: T001 | **Parallel**: yes (with T003+) | **Type**: lemma
- **Leaf**: L3. Skeleton: NormMulUnit.lean:60.

#### Statement
```lean
lemma isNormMulUnit_one_add [IsUltrametricDist A] [NormOneClass A] [CompleteSpace A]
    {x : A} (hx : ‖x‖ < 1) : IsNormMulUnit (1 + x)
```

#### Proof sketch
1. Invertibility: `u := Units.oneSub (-x) (by simpa using hx)`; `1 - (-x) = 1 + x`
   (`sub_neg_eq_add`), so `IsUnit (1 + x)`; lift to `Aˣ`.
2. `‖1 + x‖ = 1`: `hx` with `norm_one` gives `‖x‖ ≠ ‖1‖`; apply
   `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (as used at
   ForMathlib/RingTheory/LaurentPolynomial/GaussExtension.lean:195), `max_eq_left`.
3. `‖v‖ ≤ 1` for `v := (1+x)⁻¹`: from `(1+x)v = 1`: `v = 1 - x*v`, so
   `‖v‖ ≤ max ‖1‖ (‖x‖‖v‖)`; if `1 < ‖v‖` then `‖v‖ ≤ ‖x‖‖v‖ < ‖v‖`, contradiction.
4. `1 ≤ ‖v‖`: `1 = ‖(1+x)*v‖ ≤ ‖1+x‖*‖v‖ = ‖v‖`.
5. Conclude by `isNormMulUnit_of_norm_coe_inv_units` (T001) with
   `‖v‖ = 1 = ‖1+x‖⁻¹`.

#### Mathlib lemmas needed
`Units.oneSub` (Analysis/Normed/Ring/Units — verified present), `sub_neg_eq_add`,
`IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
(both in mathlib; in use in this repo), `norm_mul_le`, `norm_one`.

#### Sources
[Mar16] Remark 1.22 (txt:57–66). Note: our steps 3–4 replace the source's Neumann-series
norm computation by the algebraic `v = 1 − xv` bound (proof simplification, statement
unchanged; recorded in decomposition L3). LOC: ~30.

#### Generality decision
`[NormedRing A]`; completeness only here (matches source's standing assumption, needed
for `Units.oneSub`).

---

### [CLEANUP-1] /cleanup on PhD/Martin/NormMulUnit.lean
- **Status**: done (2026-07-28; -3 lines, gates pass, 0 warnings) | **Depends on**: T002 | **Type**: cleanup (final per-file)

---

### [T003] IsMulDistinguished: projections + NormMulClass iff
- **Status**: done (2026-07-28; term-mode constructors, no deviations) | **File**: PhD/Martin/Distinguished.lean | **Depends on**: T001 | **Parallel**: yes | **Type**: lemmas
- **Leaf**: L5. Skeleton: Distinguished.lean:46, :51.

#### Statement
```lean
lemma IsMulDistinguished.toIsDistinguished (h : IsMulDistinguished c f s) :
    IsDistinguished norm c f s
lemma isMulDistinguished_iff_isDistinguished [NormMulClass A] :
    IsMulDistinguished c f s ↔ IsDistinguished norm c f s
```

#### Proof sketch
1. `toIsDistinguished`: `⟨h.isNormMulUnit_coeff.isUnit, h.gaussNorm_eq, h.gaussTerm_lt⟩`
   (field-for-field; project structure `PowerSeries.IsDistinguished` has fields
   `isUnit_coeff`, `gaussNorm_eq`, `gaussTerm_lt` — Restricted/Distinguished.lean:38).
2. iff: `→` is 1; `←`: rebuild with `h.isUnit_coeff.isNormMulUnit` (T001).

#### Mathlib lemmas needed
None beyond T001.

#### Sources
[Mar16] Def 1.24 (txt:95–98). LOC: ~8.

#### Generality decision
Mirrors the project's `IsDistinguished` exactly so downstream proofs transport.

---

### [T004] Greatest achieving index
- **Status**: done (2026-07-28; Nat.findGreatest route; le_or_lt renamed le_or_gt in current mathlib; norm_def rfl-transparent for AchievesGaussNorm) | **File**: PhD/Martin/Distinguished.lean | **Depends on**: none | **Parallel**: yes | **Type**: lemma
- **Leaf**: L6. Skeleton: Distinguished.lean:64.

#### Statement
```lean
lemma exists_greatest_achievesGaussNorm (q : Restricted A c) (hq : q ≠ 0) :
    ∃ k₀, AchievesGaussNorm norm c q.1 k₀ ∧
      ∀ k, k₀ < k → ‖coeff k q.1‖ * c ^ k < ‖q‖
```

#### Proof sketch
1. `exists_coeff_ne_zero_norm_eq c q hq` (GaussNorm.lean:213) gives an achieving index
   with `‖q‖ > 0` (nonzero coefficient).
2. Gauss terms tend to 0 (`isRestricted_iff'` on `q.2`), so
   `{k | ‖coeff k q.1‖ * c ^ k = ‖q‖}` is contained in a finite initial segment:
   choose `N` with terms `< ‖q‖` beyond `N` (`Filter.Tendsto` + `eventually_lt`).
3. Take `k₀ :=` the max of the achieving set within `[0, N]` (`Finset.exists_max` or
   `Nat.findGreatest`); above it every term is either below `‖q‖` by maximality (≤ N)
   or by step 2 (> N). Achieving = `AchievesGaussNorm` via `norm_def`.

#### Mathlib lemmas needed
`Nat.findGreatest_spec`/`Nat.findGreatest_is_greatest` (or `Finset.exists_max_image`),
`Filter.Tendsto.eventually` + `Filter.eventually_atTop`, `norm_coeff_mul_pow_le`
(project, GaussNorm.lean:220).

#### Sources
[Mar16] txt:112–113 ("the greatest rank such that ‖q_{k₀}‖r^{k₀} = ‖q‖"). LOC: ~30.

#### Generality decision
Stated for any nonzero `q`; conclusion strict bound phrased against `‖q‖` (equal to the
`k₀` Gauss term by the achieving equation) for downstream convenience.

---

### [T005] Truncation lemmas
- **Status**: done (2026-07-28; +private coeff_toRestricted_trunc helper; norm_le_iff exists in project and is the workhorse) | **File**: PhD/Martin/Distinguished.lean | **Depends on**: T003 | **Parallel**: yes | **Type**: lemmas
- **Leaves**: L7, L8. Skeleton: Distinguished.lean:69, :75, :82.

#### Statement
```lean
lemma norm_toRestricted_trunc_le (f : Restricted A c) (N : ℕ) :
    ‖Polynomial.toRestricted c (trunc N f.1)‖ ≤ ‖f‖
lemma exists_norm_sub_toRestricted_trunc_le (f : Restricted A c) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ‖f - Polynomial.toRestricted c (trunc N f.1)‖ ≤ ε
lemma isMulDistinguished_toRestricted_trunc {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) :
    IsMulDistinguished c (Polynomial.toRestricted c (trunc (s + 1) g.1)).1 s
```

#### Proof sketch
1. Coefficients of `toRestricted c (trunc N f.1)`: equal to `coeff k f.1` for `k < N`,
   `0` otherwise (`PowerSeries.coeff_trunc`, `Polynomial.coeff_coe` /
   `Polynomial.val_toRestricted` as used at project WeierstrassDivision.lean:94).
2. First lemma: Gauss-sup over a subset of the original terms; use the project's sup
   description of the norm (`norm_def` + `gaussNorm` as `iSup`, or termwise
   `norm_coeff_mul_pow_le` + the sup characterisation).
3. Second: coefficients of the difference vanish below `N`; its norm is the sup of the
   tail Gauss terms, which are eventually `≤ ε` (tendsto-zero); choose `N` by
   `Filter.eventually_atTop`.
4. Third (L8): coefficient `s` is preserved (`s < s + 1`), so field 1 = `hg`'s; field 2:
   norm attained at `s` — `≤ ‖g_s‖cˢ` since every retained term is a `g`-term
   `≤ gaussNorm = ‖g_s‖cˢ`, and `≥` by the `s`-term itself; field 3: coefficients above
   `s` vanish and `0 < ‖g_s‖cˢ` (from `hg.gaussTerm_lt (s+1)` forcing positivity).

#### Mathlib lemmas needed
`PowerSeries.coeff_trunc` (Trunc.lean:63, verified), `Polynomial.coeff_coe`;
project: `norm_def`, `norm_coeff_mul_pow_le`, `Polynomial.val_toRestricted`,
`Polynomial.norm_toRestricted` (GaussNorm.lean:340).

#### Sources
[Mar16] txt:162–169, :173 (quotes in decomposition L7/L8). **Off-by-one**: mathlib
`trunc N` keeps coefficients `< N`, hence `trunc (s+1)` (decomposition L8 attack log).
LOC: source is 4 lines of prose → ~60 LOC for the three.

#### Generality decision
Any `f`; radius arbitrary. No `Nontrivial` needed (positivity comes from `hg`).

---

### [CLEANUP-2] /cleanup on PhD/Martin/Distinguished.lean (cadence: 3 tickets)
- **Status**: done (2026-07-28; -6 lines, gates pass) | **Depends on**: T005 | **Type**: cleanup

---

### [T006] Lemma 1.26(2): the surviving coefficient
- **Status**: done (2026-07-28; template port, norm_mul→IsNormMulUnit.norm_mul swap, inline hdom two-case) | **File**: PhD/Martin/Distinguished.lean | **Depends on**: T003, T004, CLEANUP-2 | **Parallel**: no | **Type**: theorem
- **Leaf**: L9. Skeleton: Distinguished.lean:90.

#### Statement
```lean
theorem norm_coeff_add_mul_of_isMulDistinguished {g q : Restricted A c} {s k₀ : ℕ}
    (hg : IsMulDistinguished c g.1 s) (hk : AchievesGaussNorm norm c q.1 k₀)
    (hkmax : ∀ k, k₀ < k → ‖coeff k q.1‖ * c ^ k < ‖q‖) :
    ‖coeff (s + k₀) (g * q).1‖ = ‖coeff s g.1‖ * ‖coeff k₀ q.1‖
```

#### Proof sketch
Template: project `norm_coeff_mul_pow_eq_of_dominant` (WeierstrassDivision.lean:58–71).
1. `PowerSeries.coeff_mul` writes the coefficient as `Finset.antidiagonal (s+k₀)` sum.
2. Dominance for every pair `(m, k) ≠ (s, k₀)` (source :118–137): if `k > k₀`:
   `‖g_m q_k‖ ≤ ‖g_m‖‖q_k‖` (`norm_mul_le`), then `‖g_m‖c^m ≤ ‖g_s‖c^s` (gaussNorm_eq
   as sup bound) and `‖q_k‖c^k < ‖q_{k₀}‖c^{k₀}` (hkmax + achieving eq) — multiply,
   divide by `c^{s+k₀} > 0`, strict. If `k < k₀`: then `m > s`, use
   `hg.gaussTerm_lt m` and `‖q_k‖c^k ≤ ‖q‖` (`norm_coeff_mul_pow_le`) symmetrically.
   Diagonal reference value: `‖g_s * q_{k₀}‖ = ‖g_s‖‖q_{k₀}‖` by
   `hg.isNormMulUnit_coeff.norm_mul`.
3. Ultrametric sum equality `IsNonarchimedean.apply_sum_eq_of_lt` (as at project
   WeierstrassDivision.lean:65) with peak `(s, k₀)` collapses the sum's norm to the
   diagonal's.

#### Mathlib lemmas needed
`PowerSeries.coeff_mul`, `Finset.mem_antidiagonal`, `norm_mul_le`,
`IsNonarchimedean.apply_sum_eq_of_lt` (in use at the cited project line);
project `norm_coeff_mul_pow_le`.

#### Sources
[Mar16] Lemma 1.26(2), statement txt:110–115, proof txt:116–137 (25 extracted lines).
LOC: ~70.

#### Generality decision
`k₀` and its two properties are hypotheses (supplied by T004) so the lemma is usable
both in 1.26(1) and in the preparation chain where `k₀ = 0` is derived.

---

### [T007] Lemma 1.26(1): `‖g * q‖ = ‖g‖ * ‖q‖`
- **Status**: done (2026-07-28; std axioms verified) | **File**: PhD/Martin/Distinguished.lean | **Depends on**: T006 | **Parallel**: no | **Type**: theorem
- **Leaf**: L10. Skeleton: Distinguished.lean:97.

#### Statement
```lean
theorem norm_mul_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) (q : Restricted A c) :
    ‖g * q‖ = ‖g‖ * ‖q‖
```

#### Proof sketch
1. `q = 0`: both sides `0`.
2. `≤`: `norm_mul_le` (NormedRing instance on `Restricted`).
3. `≥` (source :138–140): T004 gives `k₀`; T006 + `norm_coeff_mul_pow_le c (g*q) (s+k₀)`
   give `‖g*q‖ ≥ ‖g_s‖‖q_{k₀}‖ c^{s+k₀} = (‖g_s‖c^s)(‖q_{k₀}‖c^{k₀}) = ‖g‖‖q‖`
   (`pow_add`, achieving equations, `hg.gaussNorm_eq` + `norm_def`).

#### Mathlib lemmas needed
`norm_mul_le`, `pow_add`; project `norm_coeff_mul_pow_le`, `norm_def`.

#### Sources
[Mar16] Lemma 1.26(1), txt:116–117 and :138–140. LOC: ~25.

#### Generality decision
Stated for all `q` (the `q = 0` case is folded in), matching the source.

---

### [CLEANUP-3] /cleanup on PhD/Martin/Distinguished.lean (final)
- **Status**: done (2026-07-28; -11 lines, q=0 branch → simp, helper mul_lt_mul_of_lt_or_lt extracted) | **Depends on**: T007 | **Type**: cleanup

---

### [T008] The norm identity (1.8) and both bounds
- **Status**: done (2026-07-28; template port; note statement uses ‖g‖*‖q‖ not ‖g*q‖ — max_le_left lands directly) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T007 | **Parallel**: no | **Type**: theorems
- **Leaf**: L11. Skeleton: WeierstrassDivision.lean:33, :40, :46, :52.

#### Statement
```lean
theorem max_norm_le_of_eq_mul_add_of_isMulDistinguished … :
    max (‖g‖ * ‖q‖) ‖Polynomial.toRestricted c r‖ ≤ ‖f‖
theorem norm_eq_max_of_eq_mul_add_of_isMulDistinguished … :
    ‖f‖ = max (‖g‖ * ‖q‖) ‖Polynomial.toRestricted c r‖
theorem norm_q_le_of_eq_mul_add_of_isMulDistinguished … : ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖
theorem norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished … :
    ‖Polynomial.toRestricted c r‖ ≤ ‖f‖
```
(hypotheses each time: `hg : IsMulDistinguished c g.1 s`, `hr : r.degree < s`,
`hf : f = g * q + Polynomial.toRestricted c r` — see skeleton.)

#### Proof sketch
Template: project `max_le_norm_of_eq_mul_add` (WeierstrassDivision.lean:79–108),
which is the same statement under `[NormMulClass R]`; port with:
1. `q = 0` case unchanged.
2. Peak index: T004 (`k₀` for `q`) replaces `exists_achievesGaussNorm_dominant_max`;
   T006 replaces `norm_coeff_mul_pow_eq_of_dominant`; the `r`-coefficient at `s + k₀`
   vanishes (`Polynomial.coeff_eq_zero_of_degree_lt`, `hr` + `s ≤ s + k₀`).
3. `‖g*q‖ = ‖g‖‖q‖` via T007 wherever the template used `norm_mul`.
4. `‖f‖ ≥ ‖r‖`: ultrametric as in the template (`r = f - g*q`).
5. Equality: `≤` direction is `norm_add_le_max` + T007.
6. Bounds: `le_inv_mul_iff₀ hg.toIsDistinguished.norm_pos` etc. as in the template
   (`norm_pos` via `toIsDistinguished` and existing project API).

#### Mathlib lemmas needed
`Polynomial.coeff_eq_zero_of_degree_lt`, `IsUltrametricDist.norm_add_le_max`,
`le_inv_mul_iff₀`; project: `norm_coeff_mul_pow_le`, `Polynomial.val_toRestricted`,
`IsDistinguished.norm_pos` (via `toIsDistinguished`).

#### Sources
[Mar16] (1.8), statement txt:144–146, proof txt:147–158 (12 lines → ~80 LOC across the
four). Existing template at the cited project lines.

#### Generality decision
Completeness-free (the source proves (1.8) before using completeness); four separate
declarations per the one-conclusion rule.

---

### [T009] Division uniqueness (q and r)
- **Status**: done (2026-07-28; verbatim template port) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T008 | **Parallel**: yes (with T010+) | **Type**: theorems
- **Leaf**: L12. Skeleton: WeierstrassDivision.lean:59, :67.

#### Statement
```lean
theorem weierstrassDivision_q_unique_of_isMulDistinguished … : q₁ = q₂
theorem weierstrassDivision_r_unique_of_isMulDistinguished … : r₁ = r₂
```

#### Proof sketch
Port project `weierstrassDivision_q_unique`/`_r_unique` (WeierstrassDivision.lean:125,
:140) verbatim, swapping in T008's `norm_q_le`: apply it to
`0 = g*(q₁−q₂) + toRestricted (r₁−r₂)` (`linear_combination`, `Polynomial.degree_sub_le`
+ `max_lt`), read `‖q₁−q₂‖ ≤ ‖g‖⁻¹·0 = 0`; `r`-part by `toRestricted_injective` +
`add_left_cancel`.

#### Mathlib lemmas needed
`Polynomial.degree_sub_le`, `norm_le_zero_iff`, `sub_eq_zero`; project
`Polynomial.toRestricted_injective`.

#### Sources
[Mar16] txt:159–161. LOC: ~20.

#### Generality decision
Completeness-free, matching the source's ordering.

---

### [T010] Polynomial Euclidean division, invertible leading coefficient
- **Status**: done (2026-07-28; not in mathlib, assembled from modByMonic; GOTCHA for this file: degree_mul_le+degree_C_le path hits WithBot whnf heartbeat timeout — use smul_eq_C_mul+degree_smul_le instead) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem
- **Leaf**: L13. Skeleton: WeierstrassDivision.lean:77.

#### Statement
```lean
theorem _root_.Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff {R : Type*} [CommRing R]
    [Nontrivial R] {g₀ : Polynomial R} (hu : IsUnit g₀.leadingCoeff) (f₀ : Polynomial R) :
    ∃ q r : Polynomial R, r.degree < g₀.degree ∧ f₀ = g₀ * q + r
```

#### Proof sketch
0. FIRST search mathlib for an existing form (`lean_loogle` on the statement shape,
   names near `Polynomial.divByMonic`, `Polynomial.exists_…`); use it if found.
1. Else: `u := hu.unit`; `h := Polynomial.C ↑u⁻¹ * g₀` is monic by
   `Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one` (Monic.lean:60) with
   `↑u⁻¹ * leadingCoeff = 1` (`Units.inv_mul` after `hu.unit_spec`-rewrite).
2. `f₀ = h * (f₀ /ₘ h) + f₀ %ₘ h` from `Polynomial.modByMonic_add_div` (Div.lean:259,
   commuted); `degree (f₀ %ₘ h) < degree h` by `Polynomial.degree_modByMonic_lt`
   ([Nontrivial R], monic `h`).
3. `degree h = degree g₀` (unit `C`-multiple: `Polynomial.degree_C_mul` variant for
   unit scalars, or compute leadingCoeff ≠ 0 both ways); rearrange
   `h * d = g₀ * (C ↑u⁻¹ * d)` by commutativity: witnesses
   `q := C ↑u⁻¹ * (f₀ /ₘ h)`, `r := f₀ %ₘ h`.

#### Mathlib lemmas needed
`Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one` (verified Monic.lean:60),
`Polynomial.modByMonic_add_div` (verified Div.lean:259),
`Polynomial.degree_modByMonic_lt` (verified Div.lean:147), `Units.inv_mul`,
degree-of-unit-multiple (search `degree_C_mul`; fallback: leadingCoeff computation).

#### Sources
[Mar16] txt:170–173, citing [Lan02, IV.1.1]. **`[Nontrivial R]` is required** — trivial
ring, `g₀ = 0` counterexample; see decomposition L13 attack log. LOC: ~35.

#### Generality decision
Pure `CommRing` algebra, no norms — stated in `_root_.Polynomial` at library
generality (a mathlib-PR candidate on its own).

---

### [CLEANUP-4] /cleanup on PhD/Martin/WeierstrassDivision.lean (cadence: 3 tickets)
- **Status**: done (2026-07-28; Division saturated, binder fix, 0 warnings) | **Depends on**: T008, T009, T010 | **Type**: cleanup

---

### [T011] The contraction factor θ
- **Status**: done (2026-07-28; push_neg deprecated in current mathlib — use omega on raw negation) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T003, T005 | **Parallel**: yes | **Type**: lemma
- **Leaf**: L14. Skeleton: WeierstrassDivision.lean:85.

#### Statement
```lean
lemma exists_lt_one_norm_sub_toRestricted_trunc_le_of_isMulDistinguished
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ‖g - Polynomial.toRestricted c (trunc (s + 1) g.1)‖ ≤ θ * ‖g‖
```

#### Proof sketch
1. The difference `d := g − toRestricted (trunc (s+1) g)` has `coeff k d = 0` for
   `k ≤ s` and `= coeff k g` for `k > s` (T005 step 1 computation).
2. If `d = 0`: take `θ := 1/2` (source's own fix, txt:165–166).
3. Else `‖d‖` is attained (project `exists_coeff_ne_zero_norm_eq`) at some `t > s`, so
   `‖d‖ = ‖g_t‖c^t < ‖g_s‖c^s = ‖g‖` by `hg.gaussTerm_lt`; take
   `θ := max (1/2) (‖d‖ / ‖g‖)`: `< 1` by `div_lt_one` (`‖g‖ > 0`), `> 0` by the max,
   and the bound by `div_mul_cancel₀`.

#### Mathlib lemmas needed
`div_lt_one`, `div_mul_cancel₀`, `le_max_right/left`; project
`exists_coeff_ne_zero_norm_eq`, `norm_pos` via `toIsDistinguished`.

#### Sources
[Mar16] txt:163–166 (κ definition and the `κ = 0 → 1/2` fix). The max-with-1/2
guarantees `0 < θ`, required downstream (decomposition L14/L15 attack logs). LOC: ~30.

#### Generality decision
Bound phrased on `‖g − g'‖` directly (what L15 consumes), not on the tail sup.

---

### [T012] One-step approximate division (1.11)
- **Status**: done (2026-07-28; hθ1 unused in one-step — only iteration needs it; inline degree bookkeeping via degree_le_iff_coeff_zero) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T005, T008, T010, T011 | **Parallel**: no | **Type**: lemma
- **Leaf**: L15. Skeleton: WeierstrassDivision.lean:92.

#### Statement
```lean
lemma exists_approx_div_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθ : ‖g - Polynomial.toRestricted c (trunc (s + 1) g.1)‖ ≤ θ * ‖g‖)
    (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ ∧
      ‖f - (g * q + Polynomial.toRestricted c r)‖ ≤ θ * ‖f‖
```

#### Proof sketch
1. `f = 0`: `⟨0, 0, …⟩`.
2. Else `ε := θ * ‖f‖ > 0`; T005 gives `N` with `‖f − f'‖ ≤ ε` where
   `f' := toRestricted (trunc N f.1)`.
3. `g'p := trunc (s+1) g.1` (polynomial): `IsUnit g'p.leadingCoeff` and
   `natDegree g'p = s` from `hg` (coefficient `s` is a unit ≠ 0 — `Nontrivial A` holds
   since `‖g‖ > 0`; `degree_trunc_lt` bounds above). T010 divides:
   `trunc N f.1 = g'p * qp + rp`, `degree rp < degree g'p = s`.
4. Map along `toRestricted` (ring hom on polynomials — project
   `Polynomial.toRestricted` is additive/multiplicative on these: use
   `map_add`/`map_mul`-style project lemmas or `val`-level computation):
   `f' = g' * q + toRestricted rp` with `g' := toRestricted g'p`, `q := toRestricted qp`.
5. Bounds: `g'` is Martin-distinguished of order `s` with `‖g'‖ = ‖g‖` (T005 third
   lemma + its `gaussNorm_eq`); T008 on this division:
   `‖q‖ ≤ ‖g'‖⁻¹‖f'‖ ≤ ‖g‖⁻¹‖f‖` (T005 first lemma).
6. Error: `f − (g*q + toRestricted rp) = (f − f') + (g' − g)*q`;
   `‖(g'−g)q‖ ≤ ‖g'−g‖‖q‖ ≤ (θ‖g‖)(‖g‖⁻¹‖f‖) = θ‖f‖` (`norm_mul_le`,
   `mul_inv_cancel₀` with `‖g‖ ≠ 0`); ultrametric max of two `≤ θ‖f‖` terms.

#### Mathlib lemmas needed
`norm_mul_le`, `IsUltrametricDist.norm_add_le_max`, `mul_inv_cancel₀`,
`PowerSeries.degree_trunc_lt` (Trunc.lean:87); project `toRestricted` algebra lemmas
(`val_toRestricted` and friends around GaussNorm.lean:335–345).

#### Sources
[Mar16] (1.11) and its derivation, txt:167–186 (20 lines → ~70 LOC). `0 < θ` earns
its keep in step 2 (decomposition L15).

#### Generality decision
θ passed as hypothesis (from T011) so the density iteration T013 can fix it once.

---

### [T013] Density: `f ∈ closure (divisionSet g s)`
- **Status**: done (2026-07-28; density via AddSubgroup.dense_of_infDist_le — no completeness needed) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T012 | **Parallel**: no | **Type**: lemma
- **Leaf**: L16. Skeleton: WeierstrassDivision.lean:103.

#### Statement
```lean
lemma mem_closure_divisionSet_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) (f : Restricted A c) :
    f ∈ closure (divisionSet g s)
```

#### Proof sketch
1. Get `θ` from T011. Define recursively (source txt:187–197) `x₀ := 0 ∈ divisionSet`,
   and given `xᵢ = g*qᵢ + toRestricted rᵢ` with `‖f − xᵢ‖ ≤ θ^i‖f‖`, apply T012 to
   `f − xᵢ` and set `xᵢ₊₁ := xᵢ + (g*q' + toRestricted r')`; stays in the subgroup
   (`divisionAddSubgroup g s`, project WeierstrassDivision.lean:211, add_mem), residual
   `≤ θ^{i+1}‖f‖`.
2. `θ^i‖f‖ → 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`, `0 ≤ θ < 1`), so
   `xᵢ → f`; `mem_closure_of_tendsto` with eventual membership.
3. Implementation: induction packaged via `Nat.rec` on pairs or a `∀ i, ∃ x ∈ …`
   statement; keep it elementary (mirror `dense_divisionSet_of_forall_lt`'s style at
   project WeierstrassDivision.lean:378–407 — read it before writing).

#### Mathlib lemmas needed
`tendsto_pow_atTop_nhds_zero_of_lt_one`, `mem_closure_of_tendsto`,
`Filter.Tendsto.mul_const` (or squeeze); project `divisionAddSubgroup`.

#### Sources
[Mar16] txt:187–200. LOC: ~45.

#### Generality decision
Completeness-free (closure membership only) — matches the source, which invokes
completeness strictly after the construction.

---

### [CLEANUP-5] /cleanup on PhD/Martin/WeierstrassDivision.lean (cadence: 6 tickets)
- **Status**: done (merged into CLN-4 pass) | **Depends on**: T013 | **Type**: cleanup

---

### [T014] Closedness of the division set
- **Status**: done (2026-07-28; template port + 2 local private helpers) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T008, T009 | **Parallel**: yes (with T011–T013) | **Type**: lemma
- **Leaf**: L17. Skeleton: WeierstrassDivision.lean:110.

#### Statement
```lean
lemma isClosed_divisionSet_of_isMulDistinguished [CompleteSpace A]
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    IsClosed (divisionSet g s)
```

#### Proof sketch
Template: project `isClosed_divisionSet` (WeierstrassDivision.lean:251–282) — port,
replacing its NormMulClass bounds by T008's:
1. Sequential/filter criterion: take `xₙ = g*qₙ + toRestricted rₙ → x`.
2. Differences: `xₙ − xₘ` is a division of itself with quotient `qₙ − qₘ`, remainder
   `rₙ − rₘ` (degree `< s`); T008 `norm_q_le` gives
   `‖qₙ − qₘ‖ ≤ ‖g‖⁻¹‖xₙ − xₘ‖` ⇒ `(qₙ)` Cauchy ⇒ `q := lim` (CompleteSpace of
   `Restricted A c`, project Complete.lean:65).
3. `toRestricted rₙ = xₙ − g*qₙ → x − g*q =: ρ`; coefficients `≥ s` of each term
   vanish, coefficient functionals are continuous (project `coeff_continuous`,
   WeierstrassDivision.lean:185, NormMulClass-free) ⇒ `coeff k ρ = 0` for `k ≥ s`
   (`isClosed_setOf_coeff_eq_zero`, :195) ⇒ `ρ = toRestricted r` for a polynomial `r`
   of degree `< s` — re-derive the small extraction lemma locally (the project's
   `exists_toRestricted_eq_of_coeff_eq_zero` at :224 is `private`; ~10 LOC via
   `Polynomial.ofFinsupp`/`toRestricted` coefficientwise, or `X^s`-multiple argument;
   note a follow-up could de-privatise upstream instead — do NOT modify the existing
   file in this project).

#### Mathlib lemmas needed
`Metric.isClosed_iff_sequential` (or `IsClosed.mem_of_tendsto` route),
`cauchySeq_of_le_geometric` not needed here (differences bound directly);
project `coeff_continuous`, `isClosed_setOf_coeff_eq_zero`, `CompleteSpace` instance.

#### Sources
[Mar16] txt:198–201 (the Cauchy/limit step; see decomposition L17 for the composition
note explaining the closure packaging). LOC: ~60.

#### Generality decision
Needs `[CompleteSpace A]` — first completeness use, matching the source.

---

### [CLEANUP-ALL-1] /cleanup-all before the division milestone
- **Status**: done (2026-07-28; realised as the union of per-file cleanups CLN-1..3 + Division pass CLN-4/5/6 — only 4 project files, each individually cleaned) | **Depends on**: T001–T014, CLEANUP-1..5 | **Type**: cleanup-all

---

### [T015] **MILESTONE — Proposition 1.27: division existence**
- **Status**: done (2026-07-28; MILESTONE — Prop 1.27 proven, axioms [propext, Classical.choice, Quot.sound], lake build clean) | **File**: PhD/Martin/WeierstrassDivision.lean | **Depends on**: T013, T014, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem
- **Leaf**: L18. Skeleton: WeierstrassDivision.lean:117.

#### Statement
```lean
theorem weierstrassDivision_exists_of_isMulDistinguished [CompleteSpace A]
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r
```

#### Proof sketch
`(isClosed_… hg).closure_subset (mem_closure_… hg f)` unfolds `divisionSet`
membership to the existential (it is an `abbrev` set-builder). ~4 lines. Then
`#print axioms` check (expect `propext`, `Classical.choice`, `Quot.sound` only).

#### Mathlib lemmas needed
`IsClosed.closure_subset` (or `IsClosed.closure_eq ▸`).

#### Sources
[Mar16] Prop 1.27 statement, txt:141–146.

#### Generality decision
This IS Martin's generality: arbitrary ultrametric complete normed commutative ring,
arbitrary radius, ties below `s` allowed.

---

### [CLEANUP-6] /cleanup on PhD/Martin/WeierstrassDivision.lean (final)
- **Status**: done (merged into CLN-4 pass) | **Depends on**: T015 | **Type**: cleanup

---

### [T016] Preparation chain: the quotient's dominant constant term
- **Status**: done (2026-07-28; 4 private helpers incl greatest_achieves_eq_zero packaging k0=0; both lemmas route through 1.26(2) at k0=0) | **File**: PhD/Martin/WeierstrassPrep.lean | **Depends on**: T004, T006, T008 | **Parallel**: yes (with T011–T015 track) | **Type**: lemmas
- **Leaves**: L19, L20. Skeleton: WeierstrassPrep.lean:37, :45.

#### Statement
```lean
lemma norm_coeff_mul_norm_coeff_zero_of_eq_pow … :
    ‖coeff s g.1‖ * ‖coeff 0 q.1‖ = 1
lemma gaussTerm_lt_norm_coeff_zero_of_eq_pow … :
    ∀ k, 0 < k → ‖coeff k q.1‖ * c ^ k < ‖coeff 0 q.1‖
```
(hypotheses: `hg`, `hr : r.degree < s`,
`hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r`.)

#### Proof sketch
Order: prove the `gaussTerm_lt` lemma FIRST (source txt:230–236), then the norm product
(txt:236–241).
1. `w := toRestricted (X^s) − toRestricted r = g*q`; `q ≠ 0` since `coeff s w = 1 ≠ 0`
   (`NormOneClass` ⇒ `Nontrivial A`; `Polynomial.coeff_X_pow`, `hr` kills `r` at `s`).
2. T004 gives `k₀`; T006 gives `‖coeff (s+k₀) (g*q).1‖ = ‖g_s‖‖q_{k₀}‖ ≠ 0`; but
   `coeff (s+k₀) w = 0` for `k₀ > 0` (`w` has support ≤ s) ⇒ `k₀ = 0`. The `hkmax`
   from T004 is then the `gaussTerm_lt` conclusion (achieving eq rewrites `‖q‖` as
   `‖q₀‖c⁰`).
3. Norm product: `coeff s (g*q) = coeff s w = 1`; antidiagonal sum with diagonal
   `g_s q₀` strictly dominant (for `i ≥ 1`: `‖g_{s−i}‖c^{s−i} ≤ ‖g_s‖c^s` and
   `‖q_i‖c^i < ‖q₀‖` from step 2 — multiply and divide by `c^s`); ultrametric sum
   equality (same tool as T006) gives `‖g_s q₀‖ = ‖1‖ = 1`; rewrite by
   `hg.isNormMulUnit_coeff.norm_mul`.

#### Mathlib lemmas needed
`Polynomial.coeff_X_pow`, `Polynomial.coeff_eq_zero_of_degree_lt`, `norm_one`,
`IsNonarchimedean.apply_sum_eq_of_lt`; project `Polynomial.val_toRestricted`.

#### Sources
[Mar16] Cor 1.28 proof, txt:225–241 (quotes in decomposition L19/L20). LOC: ~80 for
the pair.

#### Generality decision
`NormOneClass` here (the `‖1‖ = 1` steps); completeness-free.

---

### [T017] The quotient is a multiplicative unit
- **Status**: done (2026-07-28; +isNormMulUnit_C and coeff-zero helpers; q = C q0 * (1+w) factorisation) | **File**: PhD/Martin/WeierstrassPrep.lean | **Depends on**: T016, T002, T001 | **Parallel**: no | **Type**: lemma
- **Leaf**: L21. Skeleton: WeierstrassPrep.lean:53.

#### Statement
```lean
lemma isNormMulUnit_of_eq_pow [CompleteSpace A] … : IsNormMulUnit q
```

#### Proof sketch
(source txt:241–248)
1. `g_s q₀ = 1 − Σ_{i≥1} g_{s−i} q_i` with norm of the sum `< 1` (T016 strictness +
   the same dominance bookkeeping); so `g_s q₀` is `IsNormMulUnit` by T002 (in `A`,
   written `1 + (−Σ)`).
2. `q₀ = g_s⁻¹ * (g_s q₀)`: `IsNormMulUnit q₀` by T001 `.coe_inv_units` + `.mul`
   (using `hg.isNormMulUnit_coeff`).
3. In `Restricted A c`: `q = C q₀ * u` where `u := C (q₀⁻¹) * q`; helper (local, part
   of this ticket): a `C`-scalar of a multiplicative unit is a multiplicative unit of
   `Restricted A c` (coefficientwise Gauss-norm computation, ~10 LOC).
4. `‖u − 1‖ < 1`: coefficient 0 of `u` is `1`; for `i > 0`,
   `‖q₀⁻¹ q_i‖c^i = ‖q₀‖⁻¹‖q_i‖c^i < 1` by T016 (mult-unit norm of `q₀⁻¹`).
5. T002 **in the ring `Restricted A c`** (instances: `NormOneClass` GaussNorm.lean:278,
   `IsUltrametricDist` :285, `CompleteSpace` Complete.lean:65) makes `u` a
   multiplicative unit; conclude `q = C q₀ * u` multiplicative by T001 `.mul`.

#### Mathlib lemmas needed
None new; instances cited above (grep-verified).

#### Sources
[Mar16] txt:241–248, display (1.12). The `C`-scalar helper is accounted here
(decomposition L21 attack log flags it explicitly). LOC: ~70.

#### Generality decision
First `CompleteSpace` use in the prep chain (via T002 in `Restricted`).

---

### [CLEANUP-ALL-2] /cleanup-all before the preparation milestone
- **Status**: done (2026-07-28; realised by per-file passes — NormMulUnit, Distinguished, Division all clean; Prep gets CLN-7/8 post-milestone + CLEANUP-FINAL sweeps everything) | **Depends on**: T015, T016, T017, CLEANUP-6 | **Type**: cleanup-all

---

### [T018] **MILESTONE — Corollary 1.28: preparation existence**
- **Status**: done (2026-07-28; MILESTONE — Cor 1.28 proven, std axioms, build clean) | **File**: PhD/Martin/WeierstrassPrep.lean | **Depends on**: T015, T017, CLEANUP-ALL-2 | **Parallel**: no | **Type**: theorem
- **Leaf**: L22. Skeleton: WeierstrassPrep.lean:63.

#### Statement
```lean
theorem weierstrassPreparation_exists_of_isMulDistinguished [CompleteSpace A]
    [NormOneClass A] {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    ∃ (ω : Polynomial A) (e : Restricted A c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsNormMulUnit e ∧
      g = e * Polynomial.toRestricted c ω
```

#### Proof sketch
(source txt:225–249)
1. T015 divides: `toRestricted (X^s) = g*q + toRestricted r`, `deg r < s`.
2. `ω := X^s − r`: monic degree `s` (`Polynomial.monic_X_pow_sub` with `hr`;
   `degree_X_pow`).
3. `toRestricted ω = g * q` (`map_sub`, rearrange `hEq`).
4. `q` multiplicative unit (T017); `e := ↑(q-unit)⁻¹` is `IsNormMulUnit` (T001
   `.coe_inv_units` in `Restricted A c` — NormOneClass instance);
   `g = e * toRestricted ω` by `Units`-algebra from step 3 (commutativity).
5. Norm clause (our documented addition, proof in decomposition L22):
   `‖toRestricted ω‖ ≤ max (c^s) ‖r‖ ≤ c^s` using `‖toRestricted (X^s)‖ = c^s`
   (`Polynomial.norm_toRestricted` + monomial Gauss norm + `norm_one`) and T008's
   r-bound on the step-1 division (`‖toRestricted r‖ ≤ ‖toRestricted (X^s)‖ = c^s`);
   `≥` from `norm_coeff_mul_pow_le` at coefficient `s` (= 1).

#### Mathlib lemmas needed
`Polynomial.monic_X_pow_sub`, `Polynomial.degree_X_pow`, `map_sub` (toRestricted is
additive — project lemma), `Units.eq_mul_inv_iff_mul_eq`-style; project
`Polynomial.norm_toRestricted`, `norm_coeff_mul_pow_le`.

#### Sources
[Mar16] Cor 1.28 statement txt:221–223, existence proof txt:225–249. LOC: ~55.
Shared-witness existential (documented exception).

#### Generality decision
`e` is asserted `IsNormMulUnit` (Martin's strength), not merely `IsUnit`.

---

### [CLEANUP-7] /cleanup on PhD/Martin/WeierstrassPrep.lean (cadence: 3 tickets)
- **Status**: done (2026-07-28; dedup coeff_mul_eq_one, -11 lines, 0 warnings) | **Depends on**: T018 | **Type**: cleanup

---

### [T019] Preparation uniqueness (ω and e)
- **Status**: done (2026-07-28; shared division-shape helper; linear_combination for omega cancel) | **File**: PhD/Martin/WeierstrassPrep.lean | **Depends on**: T009, T003 | **Parallel**: yes (independent of T015–T018) | **Type**: theorems
- **Leaf**: L23. Skeleton: WeierstrassPrep.lean:72, :82.

#### Statement
```lean
theorem weierstrassPreparation_omega_unique_of_isMulDistinguished … : ω₁ = ω₂
theorem weierstrassPreparation_e_unique_of_isMulDistinguished … : e₁ = e₂
```

#### Proof sketch
(source txt:249–252)
1. For each `i`: `ωᵢ = X^s − ρᵢ` with `ρᵢ := X^s − ωᵢ` of degree `< s`
   (monic degree-`s`: `Polynomial.degree_sub_lt`-style, `hmᵢ`, `hdᵢ`).
2. Rearrange `g = eᵢ * toRestricted ωᵢ` (unit `eᵢ`) to
   `toRestricted (X^s) = g * ↑(heᵢ.unit)⁻¹ + toRestricted ρᵢ` — a Weierstrass division
   of `X^s` by `g`.
3. T009 `r_unique` gives `ρ₁ = ρ₂` hence `ω₁ = ω₂`; `q_unique` gives
   `↑(he₁.unit)⁻¹ = ↑(he₂.unit)⁻¹` hence `e₁ = e₂` (`Units.inv_injective` /
   `inv_inv`); for `e_unique` alternatively cancel via `toRestricted ω` ≠ 0.

#### Mathlib lemmas needed
`Polynomial.degree_sub_lt` (or coefficientwise), `Units.inv_injective`,
`IsUnit.unit_spec`.

#### Sources
[Mar16] txt:249–252. `IsUnit e` suffices; no completeness (decomposition L23 —
recorded strengthening over the source). LOC: ~40 for the pair.

#### Generality decision
Hypotheses take plain `IsUnit e` — strictly stronger uniqueness than the source's.

---

### [T020] NormMulClass bridge corollaries
- **Status**: done (2026-07-28; bridges via isMulDistinguished_iff) | **File**: PhD/Martin/WeierstrassPrep.lean | **Depends on**: T003, T015, T018 | **Parallel**: no | **Type**: theorems
- **Leaf**: L24. Skeleton: WeierstrassPrep.lean:96, :103.

#### Statement
```lean
theorem weierstrassDivision_exists_of_normMulClass [NormMulClass A] [CompleteSpace A] … 
theorem weierstrassPreparation_exists_of_normMulClass [NormMulClass A] [NormOneClass A]
    [CompleteSpace A] …
```

#### Proof sketch
Rewrite `hg` through `isMulDistinguished_iff_isDistinguished` (T003) and apply
T015/T018; for the preparation corollary weaken `IsNormMulUnit e` to `IsUnit e` via
`IsNormMulUnit.isUnit`. ~6 lines each.

#### Mathlib lemmas needed
None new.

#### Sources
Bridge (no source); demonstrates that Martin's theorems subsume the project's
oracle-free `NormMulClass` statements.

#### Generality decision
Kept in the Martin folder (no changes to existing files).

---

### [CLEANUP-8] /cleanup on PhD/Martin/WeierstrassPrep.lean (final)
- **Status**: done (merged into CLN-7 pass) | **Depends on**: T020 | **Type**: cleanup

---

### [CLEANUP-FINAL] /cleanup-all on PhD/Martin/
- **Status**: done (2026-07-28; full sweep — 0 sorries/axioms/warnings across 4 files, 1068 lines, build 2171 jobs clean, endpoint axioms standard) | **Depends on**: everything above | **Type**: cleanup-all
- Also: `#print axioms` on T015/T018 endpoints; `lake build` full; then `/pre-submit`
  if a mathlib PR is intended.

## Cadence verification
20 proof tickets; per-file cleanups: NormMulUnit (1 final), Distinguished (after 3rd +
final = 2), WeierstrassDivision (after 3rd, 6th, final = 3), WeierstrassPrep (after 3rd
+ final = 2) — 8 total ≥ ⌈20/3⌉ = 7 ✓; CLEANUP-ALL before each milestone (T015, T018)
✓; CLEANUP-FINAL last ✓.
