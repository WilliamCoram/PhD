# Decomposition — LWX halo estimate (Tier 1)

Board `.mathlib-quality/lwx-halo/`. Source **[LWX]** = Liu–Wan–Xiao, *The eigencurve over
the boundary of weight space*, arXiv:1412.2584v4 (Nov 2016 numbering; the user holds the
PDF — page numbers are the PDF's printed pages). Quotes below are verbatim from it (ASCII
transliteration of the mathematics). Secondary check: none needed at this tier.

## Skeleton location

All lemmas exist as `:= by sorry` declarations (data fields honest where the design is
settled; `gFun`, `gCoeff`, `teichmuller`, `UpDatum.op` are def-holes whose bodies are
spelled in their tickets):

- `PhD/TateFredholm/TwoSidedBound.lean` (94 lines, 5 sorries)
- `PhD/LWX/HaloRing.lean` (204 lines, 42 sorries)
- `PhD/LWX/UnitsLog.lean` (101 lines, 9 sorries)
- `PhD/LWX/TiltedDegree.lean` (156 lines, 14 sorries)
- `PhD/LWX/UpMatrix.lean` (163 lines, 13 sorries)
- `PhD/LWX/Halo.lean` (153 lines, 12 sorries)

`lake build` of all six targets: **clean, sorries only** (verified 2026-09-02).

## Prior-B2 consultation (Step 4.6)

`.mathlib-quality/b2_log.jsonl` read: 2 entries — `NewtonPolygon₀.unitSlope_cases`
(degenerate-polygon falsity, resolved by representation change) and
`NewtonPolygon₀.lengths_final` (resolved). No name match and no shape match with any leaf
below (all LWX names are fresh; the one NewtonPolygon-consuming leaf, F5, uses the
post-fix `ofSlopes` API, in which the logged phantom is unrepresentable). **Clean.**

## Planning-time adversarial findings (attacks that SUCCEEDED and reshaped the plan)

1. **Composite-log attack** (kills a lazy route): estimating the coefficients of
   `z ↦ log(⟨d⟩(1+wz))/q` directly from the composite series gives
   `v(coeff_j) ≥ min_{k≥j}((k−1)−v(k))`, which at `j = pᵐ−1` is `pᵐ−1−m < pᵐ−2`
   — **strictly worse** than Lemma 3.13's shape `v ≥ (j−1)−v(j)`. Hence `qlog`
   **additivity** is load-bearing (leaf B4), exactly as the source's split
   `g = log⟨d⟩/q + log(1+(c/d)z)/q` suggests.
2. **Boundedness attack on specialization**: `ev_{T₀}(Tⁿ) = T₀ⁿ` with
   `‖T₀‖ > p⁻¹ = ‖T‖` shows `ev_{T₀}` is *not* a bounded ring hom for the gauge norm
   (only power-bounded). `charPowerSeries_baseChange` is therefore inapplicable —
   Cor 3.18 is proved coefficientwise (leaves A13/F4), which is [LWX]'s own route.
3. **Discharge attack on operator recovery**: `TateFredholm.exists_coeffEquiv`
   (Matrix.lean:134) carries `[IsTate R]`, which `HaloInt p` does not satisfy. The
   operator `UpDatum.op` is therefore **constructed directly** (leaf D6: termwise tsum,
   with summability from `φ ∈ c(·)` decay and entry norms `≤ 1`), not recovered.

---

## Result R1 — Theorem 3.16 (the halo estimate)

### Source proof read (Step 1)

[LWX] pp. 15–22. The chain: Prop 3.1 (p. 16) writes `U_p` as a `t×t` matrix of
operators `‖_δ`, `δ ∈ (pZp Zp; qZp Z×p)`; Prop 3.4 (p. 17) computes the Mahler matrix
of one `‖_δ` as `P_{m,n}(δ) = Δ̃^(m)(((az+b)/(cz+d) choose n)·[cz+d])|_{z=0}`; §3.5
(p. 17) lists the difference-calculus identities (3.5.1)–(3.5.4); Def 3.6/Lemma 3.7
(p. 18) polynomial functions; Def-Prop 3.8 (p. 18) tilted degree; Lemma 3.10 (p. 18)
its calculus; Lemmas 3.11–3.13 (pp. 19–20) the three estimates; Prop 3.14 (p. 21) the
entry bound, via the expansion `[cz+d] = [d₀]·(1+T)^{g(z)}`, `g = log((cz+d)/d₀)/q`;
Lemma 3.15 (p. 21) the ring `Λ^{>1/p}`; Thm 3.16 (pp. 21–22) assembles: well-definedness
of `Char(P)` by mod-`𝔪^r` triangularity, then the diagonal conjugation
`P' = D P D⁻¹`, `D = diag(1..1,T..T,T²..)`, whose `n`-th column lies in
`T^{⌊n/t⌋−⌊n/pt⌋}Λ^{>1/p}`, giving `c_n ∈ T^{λ(n)}Λ^{>1/p}`.

Prose proof (ours, mirroring the source): *(i)* build the coefficient ring `Λ^{>1/p}`
with its `T`-adic gauge norm (Lemma 3.15 as `‖·‖ ≤ p^{−k} ⟺ T^k | ·`); *(ii)* define
the entry `P_{m,n}(δ)` by its `T`-coefficient stream (Prop 3.4 + the Prop 3.14-proof
expansion) and prove `‖P_{m,n}(δ)‖ ≤ p^{−(m ∸ ⌊n/p⌋)}` from tilted degrees `⌊n/p⌋` for
`(f choose n)` (Lemma 3.12), `r` for `(g choose r)` (Lemma 3.13 via the additivity
split), multiplied by Lemma 3.10(2) and read off at `z = 0`; *(iii)* the block matrix
on `ι × ℕ` then has the two-sided bound `‖M_{(i,m),(j,n)}‖ ≤ p^{−(m ∸ ⌊n/p⌋)}`
((3.16.2) blockwise); *(iv)* the source's conjugation step is executed at the minor
level: each Leibniz monomial of `minor S` picks one entry per row and per column of
`S`, and for `π ∈ Perm S`, `Σ_S w'∘π = Σ_S w'`, so
`‖minor S‖ ≤ p^{−(Σ_S m − Σ_S ⌊m/p⌋)}`; the monotone weight `m − ⌊m/p⌋` is minimised
by initial fill, `Σ_{k<n}(⌊k/t⌋ − ⌊k/pt⌋) = λ(n)`; ultrametric summability of the
minors gives well-definedness and `‖c_n‖ ≤ p^{−λ(n)}` at once.

**Faithfulness note (binding honesty).** Step *(iv)* implements the identical
computation as the source's conjugation — the exponent bookkeeping is literally the
same sums — but stays in the integral ring by using invariance of principal minors
under diagonal conjugation (`det(D_S M_S D_S⁻¹) = det M_S`) instead of forming `P'`
over a ring with `T⁻¹`. The source's own justification of `Char(P) = Char(P')` is the
same determinant-level fact. Recorded here so no reviewer mistakes it for an invented
route: every exponent in *(iv)* has its display in the source's Thm 3.16 proof.

### Leaf clusters

Sizing convention: "source: N lines" counts the display lines of the cited proof in
the PDF; Lean estimates are anchored on them.

---

#### A — the ring `Λ^{>1/p}` (`PhD/LWX/HaloRing.lean`) — **API gap AG2, own sub-tree**

The source's Lemma 3.15 is one line; the ring construction cost is formalisation-
intrinsic (no mathlib Iwasawa/halo objects — verified: no `LaurentSeries`/`HahnSeries`
shape matches the coefficient-bound carrier). Sub-tree:

- **A1** (leaves, cluster): carrier + `Zero/One/Add/Neg/Mul` bound fields +
  `CommRing` proof fields + `summable_mul_coeff` (HaloRing.lean:66–128).
  - Source: [LWX, Lemma 3.15] p. 21 — "The rigid space associated to the ring
    `Λ^{>1/p} := ΛJpT⁻¹K = ZpJT, pT⁻¹K ⊗Zp Zp[∆]` is `W^{>1/p}`"; coefficientwise
    description from [LWX, Cor 3.18 proof] p. 23 — "First note that if
    `Σ_{m∈Z} d_m T^m ∈ Λ^{>1/p}`, then `v(d_m) ≥ max{0, −m}`."
  - Lean ↔ source: `HaloInt p` *is* the set of streams with `v(d_j) ≥ max(0,−j)`
    (bound field `‖d j‖ ≤ p^{min(0,j)}`), with convolution product = multiplication of
    `T`-expansions. The `⊗ Zp[∆]` factor is deliberately dropped (per-ω; plan.md §1).
  - Discharges: closure of bounds under `+`/convolution = ultrametric triangle +
    `max(0,−i) + max(0,i−k) ≥ max(0,−k)`; summability of the convolution =
    `TateFredholm.summable_of_tendsto_cofinite` (verified, Tate.lean:405) with both
    tails killed by the bound; `mul_assoc`/`mul_comm`/distrib = tsum manipulation:
    `Equiv` reindexing (`Equiv.subLeft`), `Summable.tsum_prod`-style Fubini and
    `tsum_mul_tsum_of_summable_norm` (verified, Analysis/Normed/Ring/InfiniteSum:70).
  - Attacks attempted:
    - [edge] `k`-th product coefficient at `f = g = 1`: convolution of deltas gives
      `1` at `0` — matches `coeff_one`. `f = T, g = T⁻¹`? — `T⁻¹ ∉ HaloInt` (bound
      fails at `j = −1`… `v(1) = 0 ≥ max(0,1)` false) ✓ the ring correctly does NOT
      contain `T⁻¹` (it must not — attack on "is `T` a unit": if it were, `IsTate`
      would be free and finding 3 above would be moot; `1 = T·g` forces
      `g j = 1_{j=−1}`, excluded — consistent).
    - [hypothesis] Is the bound `v(d_j) ≥ max(0,−j)` over- or under-specified vs the
      source? Under LWX `Λ^{>1/p} = ZpJT,pT⁻¹K`: monomials `T^i(pT⁻¹)^j` have
      coefficient `p^j` at `T^{i−j}`, i.e. `v = j ≥ max(0,j−i)` ✓; conversely any
      bounded stream is `Σ_j u_j·(pT⁻¹)^{−m}`-assembled (checked by hand for `m<0`
      and `m≥0` separately). No drift.
    - [counterexample search on associativity route] ℤ-indexed Cauchy product has no
      off-the-shelf mathlib lemma (`tsum_mul_tsum_eq_tsum_sum_antidiagonal` is
      ℕ-only — verified) — the discharge is by Fubini over `ℤ×ℤ` fibers of
      `(i,j) ↦ i+j`; the needed norm-summability over the product holds since each
      factor's weighted norms are `≤ 1` and cofinitely small (three-factor version
      for assoc). Risk accepted and priced (this is the board's largest single
      ticket, A1).
  - Sizing: source 1 line; construction ~350 LOC Lean (pattern: `cSpace`/`C₀`
    builds).
- **A2** (leaves, cluster): the norm layer — `NormedRing` fields, `norm_def`,
  `norm_le_one`, `norm_coeff_le_norm`, `NormOneClass`, `IsUltrametricDist`
  (HaloRing.lean:130–170).
  - Source: [LWX, Lemma 3.15] — "The ideal `𝔪_Λ Λ^{>1/p}` is the same as the
    principal ideal `(T)`"; the gauge norm is that filtration with `‖T‖ = p⁻¹`.
  - Lean ↔ source: `‖f‖ = ⨆ j ‖f j‖·p^{−j}` is the `(T)`-adic gauge: `‖f‖ ≤ p^{−k}`
    iff `f ∈ T^k·HaloInt` (leaf A4). Bounded above by 1 (bound field), so the `⨆`
    is honest.
  - Attacks: [edge] `f = 0` (iSup of zeros over nonempty ℤ = 0 ✓ — `Real.iSup`
    junk-safety checked: family is bounded and nonneg); [hypothesis] is
    `norm_mul_le` an equality (Gauss)? Likely yes but only `≤` is claimed — weaker,
    safe; [source-drift] `‖T‖ = p⁻¹` is a normalisation choice (any `c ∈ (0,1)`
    works); chosen so `const` is isometric — recorded in the file docstring, no
    source conflict (source uses the ideal filtration, normalisation-free).
  - Sizing: ~150 LOC.
- **A3** (leaves): `CompleteSpace` (coefficientwise limits).
  - Attacks: [edge] Cauchy sequence with drifting support (e.g. `T^{-n}`-shifted
    bumps) — excluded because norms would blow up; the uniform bound forces
    coefficientwise convergence *within* the bound. [discharge] mathlib-complete
    `ℤ_[p]` per coefficient + uniform-convergence glue; standard.
  - Sizing: ~80 LOC.
- **A4** (leaves): `T`, `coeff_T_mul`, `norm_T_mul`, `norm_le_zpow_iff`,
  `exists_T_pow_mul_of_norm_le`, `norm_le_of_eq_T_pow_mul`, `const`, `norm_const`,
  `const_mul` (HaloRing.lean:141–186).
  - Source: [LWX, Lemma 3.15] proof — "This is clear, noting that `p = pT⁻¹ · T`."
  - Lean ↔ source: `T^k`-divisibility ⇔ `‖·‖ ≤ p^{−k}` ⇔ coefficientwise
    `v(d_j) ≥ max(k−j, 0)` is the entire content of "𝔪-power = (T)-power" that
    Thm 3.16/Cor 3.18 consume.
  - Attacks: [edge] `k = 0` (trivial ✓); `f = 0` (`g := 0` witnesses ✓);
    [hypothesis] does `exists_T_pow_mul` need summability care? No: `T^k·g` is a
    pure shift (proved via `coeff_T_mul` iterated), and the candidate `g` is the
    shifted stream, whose bound field is exactly the norm hypothesis. [discharge]
    all internal.
  - Sizing: ~120 LOC.
- **A5** (leaves): `specialize`, `summable_specialize`, `norm_specialize_le`,
  `specialize_one` (HaloRing.lean:188–204). Quoted and attacked under R2 (F4/A13)
  below, where they are consumed.

#### B — Teichmüller and the logarithm (`PhD/LWX/UnitsLog.lean`) — **API gap AG1**

- **B1** (leaf): `teichmuller`, `teichmuller_mul`,
  `norm_mul_teichmuller_inv_sub_one_le`, `oneUnitPart` (UnitsLog.lean:38–58).
  - Source: [LWX, Notation 2.1] p. 8 — "We write `Z×p` as `∆ × (1 + qZp)×` with
    `∆ ≅ (Z/qZ)×`."
  - Lean ↔ source: the splitting is realised by the Teichmüller lift
    `ωT(x) = lim x^{pⁿ}`; the source assumes it silently (standard). NOT in mathlib
    (verified: `WittVector.teichmuller` is the Witt-vector section, not this;
    nothing for `ℤ_[p]ˣ`).
  - Discharge plan: completeness of `ℤ_[p]` + `‖x^{p^{n+1}} − x^{pⁿ}‖ ≤ p^{−(n+1)}`
    (Frobenius contraction, from `a ≡ b [p^n] → a^p ≡ b^p [p^{n+1}]` — mathlib has
    the binomial-expansion pieces); multiplicativity by limits.
  - Attacks: [edge] `x = 1` (`ωT = 1` ✓); `p = 2`: `x^{2ⁿ} → 1` always, splitting
    degenerates — consistent with the board's `p ≠ 2` scope (B1 itself is stated
    without `p ≠ 2`; the *limit* still exists, lands in `μ_{p−1}`; fine). [shape vs
    b2 log] no match. [discharge] the contraction estimate cited is standard;
    verified `PadicInt.norm_le_pow_iff_mem_span_pow` exists for the divisibility
    reading.
  - Sizing: source 0 lines (assumed); ~120 LOC.
- **B2** (leaves): `qlog`, `summable_qlog`, `norm_qlog_le` (UnitsLog.lean:60–77).
  - Source: [LWX, Notation 2.1] — "We identify `(1 + qZp)×` with `Zp` via
    `(1/q) log(−)`" (at `q = p`).
  - Attacks: [edge] `u = 1` (`qlog 1 = 0` ✓ all terms vanish); [hypothesis] `p ≠ 2`
    needed only for `norm_qlog_le`'s margin (`k − v(k) ≥ 1`): at `p = 2, k = 2` the
    term `(u−1)²/2` has `v ≥ 2·1−1 = 1` — actually still fine, but at `p=2`
    `q = 4` changes the normalisation; scope-consistent. [discharge]
    `summable_of_tendsto_cofinite` on `ℚ_[p]`-terms with `v ≥ k − v(k) → ∞` ✓.
  - Sizing: ~80 LOC.
- **B4** (leaf): `qlog_mul` (UnitsLog.lean:84).
  - Source: [LWX, Prop 3.14 proof] p. 21 — "Write `d = d0 · ⟨d⟩` … so that `[cz+d]`
    can be written as `[d0] · (1 + T)^{log((cz+d)/d0)/q}`. Put
    `g(z) = log((cz + d)/d0)/q`; it is of the form considered in Lemma 3.13."
    The "form" requires the split `log⟨d⟩ + log(1 + (c/d)z)` — i.e. additivity.
  - Load-bearing per planning finding 1 (the composite estimate fails at `k = pᵐ`).
  - Discharge plan: standard power-series identity; on `1 + pℤ_p` prove
    `exp∘qlog = id`-free route: differentiate-free double-series rearrangement, or
    the classical `log(uv) − log u − log v` vanishing by binomial manipulation. The
    fork's `PhD/JacobsSlash/1_PadicAnalytic.lean` has the exp/log pair with the
    cocycle at `‖3‖`-generality — its proofs are the pattern (project discharge
    pattern, not import).
  - Attacks: [counterexample] additivity fails outside the domain (`‖u−1‖ = 1`) —
    hypotheses `‖u−1‖ ≤ p⁻¹`, `‖v−1‖ ≤ p⁻¹` present ✓ (and `‖uv−1‖ ≤ p⁻¹` follows,
    checked: `uv−1 = (u−1)(v−1)+(u−1)+(v−1)`). [edge] `v = u⁻¹`. [sizing risk]
    honest: this is the analytically fiddliest leaf of tranche B; budgeted 150 LOC.
- **B5** (leaves): `IsLogShape`, `qlogLinearCoeff`, `isLogShape_qlogLinearCoeff`,
  `hasSum_qlogLinearCoeff`, `IsLogShape.add_const` (UnitsLog.lean:79–101).
  - Source: [LWX, Lemma 3.13] p. 19 — "For a function
    `f(z) = a0 + a1z + pa2z²/2 + p²a3z³/3 + · · · + p^{k−1}ak z^k/k + · · ·` with
    `an ∈ Zp`" — `IsLogShape` is that coefficient shape, stated in `ℚ_p` with norms
    (`‖A_k‖·‖k‖ ≤ p^{1−k}`), dodging element-level division.
  - Lean ↔ source: `A_k = p^{k−1}a_k/k` with `a_k ∈ ℤ_p` ⟺ `v(A_k) ≥ (k−1)−v(k)`
    ⟺ our inequality; `A_0, A_1` free integral ✓ matches (`a_0` and `a_1z` terms).
  - Attacks: [edge] `k = 1`: bound reads `‖A_1‖·1 ≤ p⁰ = 1` ✓ integral, matches
    source's plain `a_1`; [source-drift] the source's `f` maps to `ℤ_p` — our
    `hasSum` into `(F z : ℚ_[p])` with `F : ℤ_[p] → ℤ_[p]` keeps that;
    [discharge] `isLogShape_qlogLinearCoeff` is `v(w^k/k) ≥ k − v(k) ≥ (k−1)−v(k)`
    ✓ one-line valuation arithmetic.
  - Sizing: ~90 LOC.

#### C — tilted degree (`PhD/LWX/TiltedDegree.lean`)

- **C1** (leaf): `fwdDiff_iter_mul` (TiltedDegree.lean:44).
  - Source: [LWX, (3.5.1)] p. 17 —
    "`Δ̃^(m)(fg)(z) = Σ_{i=0}^m (m i) Δ̃^{(m−i)}(f)(z + i) Δ̃^{(i)}(g)(z)`" ("can be
    checked easily").
  - Discharge: induction on `m`; base `rfl`; step via Pascal. Mathlib has
    `fwdDiff_add`, `fwdDiffₗ` linear algebra (verified) but no product rule
    (verified absent) — genuine leaf, PR candidate.
  - Attacks: [edge] `m = 0` (`rfl`-shape ✓), `f ≡ 1` (collapses to `Δ̃^m g` via
    `choose`-sum ✓ sanity); [hypothesis] needs only `CommRing` target — stated so;
    [b2] no match.
  - Sizing: source 1 display; ~40 LOC.
- **C2** (leaves): `fwdDiff_choose`, `fwdDiff_iter_choose` (TiltedDegree.lean:52–63).
  - Source: [LWX, (3.5.2)] p. 17 — "`Δ̃^(m)(z choose n) = (z choose n−m)` if `n ≥ m`,
    `0` otherwise."
  - Discharge: `mahler`-density: both sides continuous (`PadicInt.continuous_choose`,
    verified), agree on `ℕ` by `Nat.succ_sub_one`+Pascal (`Nat.choose_symm_diff`
    family), conclude by `PadicInt.denseRange_natCast` (verified, used the same way
    in mathlib's `MahlerBasis` at line 346).
  - Attacks: [edge] `n = 0` (`Δ̃1 = 0` ✓ second branch), `m = n` (constant `1` ✓);
    [discharge] verified the density lemma + continuity exist by grep; [drift] none.
  - Sizing: ~50 LOC.
- **C3** (leaf): `fwdDiff_iter_eval_eq_zero` (TiltedDegree.lean:69).
  - Source: [LWX, Lemma 3.7(1)] p. 18 (the vanishing direction) — polynomial of
    degree `≤ n` has `Δ̃^{(n+1)} = 0`.
  - Discharge: induction on degree: `z ↦ P(z+1) − P(z)` has `natDegree < natDegree P`
    (leading terms cancel; mathlib `Polynomial` arithmetic).
  - Attacks: [edge] `P = C c` (`m = 1`: `Δ̃(const) = 0` ✓); constant `m = 0` excluded
    by `hdeg : natDegree < m` ✓; [hypothesis] over any `CommRing` ✓ stated so.
  - Sizing: ~35 LOC.
- **C4** (leaves): `TiltedDeg`, `tiltedDeg_iff_of_forall_norm_le`,
  `TiltedDeg.of_fwdDiff`, `TiltedDeg.mul`, `TiltedDeg.of_tendsto`
  (TiltedDegree.lean:73–110).
  - Source: [LWX, Def-Prop 3.8] p. 18 — "(1) for any `m ∈ N`, `Δ̃^(m)(f)` is a
    (continuous) function on `Zp` that takes value in `p^{m−n}Zp`"; [LWX, Lemma
    3.10(2)] p. 18 — "If `f` and `g` … of tilted degree `≤ m` and `≤ n` … `fg` has
    tilted degree `≤ m + n`", proved by the (3.5.1) display: "Each term on the right
    hand side has valuation at least `(r − i − m) + (i − n) = r − m − n`."
  - Lean ↔ source: definition by clause (1) only (design decision; clause (2) and
    (3.5.4) are consumed nowhere downstream — checked against every later use in the
    source's §3: Prop 3.14 uses values of `Δ̃^m(...)` at `z = 0`, i.e. clause (1)).
  - Attacks: [composition] could `mul` fail where the source's proof uses clause (2)?
    Re-read p. 18: the displayed proof of 3.10(2) uses (3.5.1) + clause (1)
    pointwise — exactly our route ✓ no clause-(2) dependence. [edge] `m = 0` in
    `of_fwdDiff` guarded by `1 ≤ n` ✓; `TiltedDeg n f` for `f` non-integral —
    impossible, `f : ℤ_[p] → ℤ_[p]` ✓. [limit leaf] pointwise suffices since
    `Δ̃^m f z` is a finite signed combination of values (fwdDiff_iter_eq_sum_shift,
    verified) — no uniformity needed, *stronger* than the source's approximation
    step needs.
  - Sizing: source ~12 lines; ~120 LOC.
- **C5** (leaf): `exists_binomial_basis` (TiltedDegree.lean:118).
  - Source: [LWX, Lemma 3.11] p. 19 — "Let `g(z) = b0 + b1z + · · · + brz^r ∈ Zp[z]`.
    If there exists some `s ∈ R≥0` such that `v(bi) ≥ is` for all `i`, then we can
    rewrite `g(z)` as `Σ ci · i! (z choose i)` with `v(ci) ≥ is`." Proof: reverse
    induction on the triangular change of basis, "where `αi,j` are the coefficients
    of `z^j` in the product `z(z−1)···(z−i+1)`, which is of course an integer."
  - Lean ↔ source: norm form (`ρ = p^{−s}`) over any ultrametric field — this
    absorbs the source's fractional `s` (its Lemma 3.13 use has `s = (n−1−v(n))/n`
    and coefficients in `Zp[p^{1/n}]`) without ever leaving `ℚ_p`: only norms of the
    `c_i` are ever used. Generality gain documented; no content drift.
  - Attacks: [edge] `P = 0` (`c ≡ 0` ✓), `deg 0` (`c_0 = b_0` ✓); [hypothesis] field
    needed only for `i!⁻¹` in `binomialPoly` ✓ minimal; [discharge]
    `descPochhammer` verified in mathlib (`RingTheory/Polynomial/Pochhammer`);
    triangularity = `Polynomial` coeff arithmetic.
  - Sizing: source 10 lines; ~70 LOC.
- **C6** (leaves): `nat_ineq_3_12`, `tiltedDeg_choose_of_pMul`
  (TiltedDegree.lean:124–139).
  - Source: [LWX, Lemma 3.12] p. 19 — "For a function
    `f(z) = a0 + pa1z + p²a2z² + · · · ∈ ZpJpzK` and an integer `n ≥ 0`, the
    expression `(f(z) choose n)` has tilted degree `≤ ⌊n/p⌋`." Proof: "By
    approximation, we may assume that `f(z)` is a polynomial. Put
    `g(z) = f(z)(f(z) − 1)···(f(z) − n + 1)` … By Lemma 3.11 … it suffices to prove
    that when `k > ⌊n/p⌋`, `v(k!p^k/n!) ≥ k − ⌊n/p⌋`. To this end, note that in this
    case `⌊k/p^ℓ⌋ ≥ ⌊n/p^{ℓ+1}⌋` for any `ℓ ∈ N`."
  - Lean ↔ source: hypothesis phrased as a coefficient stream with
    `‖a_k‖ ≤ p^{−k}` + `HasSum` presentation (= `ZpJpzK` read pointwise);
    conclusion identical. The `nat_ineq_3_12` leaf is the displayed factorial
    estimate, in `Nat.factorization` form; Legendre = `padicValNat_factorial`
    (verified, `NumberTheory/Padics/PadicVal/Basic.lean:572`).
  - Attacks: [edge] `n = 0` (`(f choose 0) = 1`, tilted `0` ✓), `n < p` (`⌊n/p⌋ = 0`:
    claims `(f choose n)` tilted `0`, i.e. all `Δ̃^m` integral-with-margin `p^{−m}`…
    for `m ≥ 1` this needs the *full* mechanism, not trivial — good, no vacuity);
    [hypothesis] is `a_0` unrestricted? Source has `a_0` free ✓ ours too (`k = 0`
    bound `‖a_0‖ ≤ 1`); [composition] the polynomial-approximation step consumes
    C4's `of_tendsto` with truncated series — pointwise convergence from summability
    ✓.
  - Sizing: source 14 lines; ~130 LOC total.
- **C7** (leaves): `nat_ineq_3_13_2`, `tiltedDeg_choose_of_logShape`,
  `tiltedDeg_choose_monomial_p` (TiltedDegree.lean:141–156).
  - Source: [LWX, Lemma 3.13] pp. 19–20. Statement quoted at B5. Proof: "by the
    binomial identity (3.5.3) together with the additive property of the tilted
    degree (Lemma 3.10), we may assume that `f(z) = p^{n−1}anz^n/n` is a monomial …
    (3.13.2) `v(k!) + m ≥ v(m!) + (1 + v(n))k/n`. We separate several cases: (a) if
    `p ∤ n` … (b) If `n ≥ 2p` and `(p, n) ≠ (2, 4)` … (c) If `n = p` … show directly
    that `(ap^{p−2}z^p choose m)` has tilted degree `≤ m` … by induction on `m` …
    note that `ap^{p−2}((z + 1)^p − z^p) ∈ Zp[pz]`; so Lemma 3.12 shows the first
    factor has tilted degree `≤ ⌊j/p⌋ ≤ j − 1`."
  - Lean ↔ source: the case-(d) `(p,n) = (2,4)` branch is vacuous at `p ≠ 2` — the
    scope hypothesis kills it, and case (b)'s exclusion `(p,n) ≠ (2,4)` is
    automatic. Monomial reduction = Chu–Vandermonde `Ring.add_choose_eq` (verified,
    Binomial.lean:519; commutative, so `Commute` trivial) iterated + `TiltedDeg.mul`
    + `of_tendsto`. Case (c) = `tiltedDeg_choose_monomial_p`, consuming C6.
  - Attacks: [edge] `m = 0` (void, per source), `n = 1` ("the easy bound": polynomial
    of degree `m` — consumes C3+C5); [composition] does the monomial reduction
    really cover mixed `f`? (3.5.3) splits `binom(Σ f_i, m)` into products over
    compositions — infinitely many summands for a series: handled as the source
    does, polynomial-first then `of_tendsto` ✓; [inequality check] (3.13.2) at
    `p = 3, n = 3, m = 1, k = 2`: LHS `2·(1+1)/3 = 4/3`, RHS `v(2!)+1−0 = 1` —
    fails?! Re-read: case (c) `n = p` is *excluded* from (3.13.2) ("the inequality
    (3.13.2) might fail. So we have to go back…") ✓ our `nat_ineq_3_13_2` must carry
    the case-(a)/(b) guards; the skeleton's bare `2 ≤ n` is **too strong a claim**
    — the ticket (C7) records the corrected hypotheses (`p ∤ n` or `2*p ≤ n`), and
    the skeleton statement is to be adjusted at ticket C7 start. **[attack
    SUCCEEDED — statement fix queued]** (This is exactly what the pass is for; the
    fix is confined to one leaf's hypotheses, the tree shape is unchanged.)
  - Sizing: source ~45 lines; ~260 LOC total (largest analytic ticket).

#### D — the entries and the operator (`PhD/LWX/UpMatrix.lean`)

- **D1** (leaves): `LocalMat`, `mobiusFun`, `isUnit_c_mul_add`,
  `exists_hasSum_mobiusFun` (UpMatrix.lean:44–83).
  - Source: [LWX, Prop 3.1(3)] p. 16 — "Each `δp` appearing above belongs to
    `(pZp Zp; qZp Z×p)`"; [LWX, Prop 3.14 proof] p. 21 — "Put
    `f(z) = (az + b)/(cz + d) ∈ ZpJzK` … In case (1), we have `f(z) ∈ ZpJpzK`."
  - Lean ↔ source: `LocalMat` carries exactly `(pZp, Zp; pZp, Z×p)` (`q = p`);
    `exists_hasSum_mobiusFun` = "`f(z) ∈ ZpJpzK`" with the coefficients produced by
    geometric expansion of `(cz+d)⁻¹`.
  - Attacks: [edge] `c = 0` (series is a polynomial `az/d + b/d`… coefficients:
    `k=0: b/d` integral ✓, `k=1: a/d ∈ pℤ_p` ✓, rest 0 ✓); [coefficient check]
    `k`-th coefficient `(a(−c/d)^{k−1}·d⁻¹ + b(−c/d)^k·d⁻¹)`-shape has
    `v ≥ min(1+(k−1), k) = k` ✓ (both `a` and `c` carry `v ≥ 1`); [hypothesis] is
    `det ≠ 0` needed (source's `M₁` has it)? Not for the series or bounds — omitted,
    documented; [drift] none.
  - Sizing: ~110 LOC.
- **D2** (leaves): `gFun`, `gCoeff`, `isLogShape_gCoeff`, `hasSum_gCoeff`
  (UpMatrix.lean:85–105); def-holes with ticket-specified bodies
  (`gFun δ z = ((qlog (oneUnitPart δ.d) + qlog (1 + (c·d⁻¹)z))/p`-integralised;
  `gCoeff = qlogLinearCoeff (c·d⁻¹)` shifted by the constant).
  - Source: [LWX, Prop 3.14 proof] p. 21 — "Put `g(z) = log((cz + d)/d0)/q`; it is
    of the form considered in Lemma 3.13."
  - Lean ↔ source: `(cz+d)/d₀ = ⟨d⟩·(1 + (c/d)z)` since `c ∈ pℤ_p`; additivity (B4)
    splits `g` into the constant `qlog⟨d⟩/p` + the linear-composite stream (B5);
    `IsLogShape.add_const` closes the shape.
  - Attacks: [domain] is `1 + (c/d)z ∈ 1 + pℤ_p` for all `z`? `‖c·d⁻¹·z‖ ≤ p⁻¹` ✓;
    [integrality of `/p`] `v(qlog(...)) ≥ 1` from B2's margin ✓ at `p ≠ 2`;
    [composition] `hasSum_gCoeff` = B5's `hasSum` + constant shift ✓.
  - Sizing: ~90 LOC.
- **D3** (leaves): `entryCoeff`, `entry` (bound field), `norm_entryCoeff_le`,
  `norm_entry_le` (UpMatrix.lean:107–140).
  - Source: [LWX, Prop 3.4] p. 17 —
    "`P_{m,n}(δp) = Δ̃^(m)( ((az+b)/(cz+d) choose n) · [(cz + d)] )|_{z=0}`";
    [LWX, Prop 3.14] p. 21 — "When `δp ∈ (pZp Zp; qZp Z×p)`, the coefficient
    `P_{m,n}(δp)` belongs to `𝔪_Λ^{max{m−⌊n/p⌋,0}}`", via "the `T^r`-coefficients of
    (3.4.1) ha[ve] valuation at least `m − ⌊n/p⌋ − r`".
  - Lean ↔ source: **Prop 3.4 is definitional here** — the stream *is* the entry;
    that it computes the `‖_δ`-action on `S^D_int` is the deferred model seam
    (plan.md, "Deferred seams" 1). The bound chain: Lemma 3.12 gives
    `TiltedDeg ⌊n/p⌋ (choose(f, n))` (D1 feeds the hypothesis), Lemma 3.13 gives
    `TiltedDeg r (choose(g, r))` (D2 feeds), `TiltedDeg.mul` adds, clause (1) at
    `z = 0` reads off `v ≥ (⌊n/p⌋ + r) − m`… sign-checked: tilted degree
    `≤ ⌊n/p⌋ + r` gives `‖Δ̃^m(...)(0)‖ ≤ p^{(⌊n/p⌋ + r) − m}` ✓ matches the
    skeleton's exponent `(n/p : ℤ) + r − m`; packaging by `norm_le_zpow_iff` (A4).
  - Attacks: [edge] `r = 0` (`choose(g,0) = 1`: entry = pure Lemma-3.12 bound ✓);
    `m = 0` (bound `≥ 1`, trivial ✓ consistent with `max{·,0}`); [unit factor] the
    `ω(d̄)` scalar has norm 1 — doesn't perturb bounds ✓; [drift] the source's
    `[d₀]` is the ω-value at the Teichmüller part; `d̄ = toZMod d` and
    `ω : (ZMod p)ˣ →* ℤ_[p]ˣ` composes to the same data ✓.
  - Sizing: source ~25 lines; ~160 LOC.
- **D5** (leaves): `UpDatum`, `UpDatum.matrix`, `UpDatum.norm_matrix_le`,
  `UpDatum.tendsto_matrix_cofinite` (UpMatrix.lean:142–158).
  - Source: [LWX, Prop 3.1(1)] p. 16 — "Each entry of `Up` is a sum of operators of
    the form `‖_δp` … There are exactly `p` such operators appearing in each row";
    [LWX, (3.16.2)] p. 22 — "`P_{m,n} ∈ 𝔪_Λ^{max{⌊m/t⌋−⌊n/pt⌋,0}}`" (flattened
    indexing; blockwise it is the `(m, n)`-bound uniform in the block pair, which is
    what `norm_matrix_le` states).
  - Attacks: [column-count drop] Prop 3.1(2) ("each column") is *not* carried —
    verified unused in the Thm 3.16 proof (only row structure and (3)'s shape
    enter); [empty filter] a block pair with no `j` mapping gives entry `0` ✓ bound
    holds; [cofinite decay] for fixed column `(j,n)`: bound `p^{−(m−⌊n/p⌋)} → 0` as
    `m → ∞`, and the finitely many rows per `m`-level are handled by `Fintype ι` ✓.
  - Sizing: ~90 LOC.
- **D6** (leaves): `UpDatum.op`, `UpDatum.matrixCoeff_op` (UpMatrix.lean:160–163);
  def-hole, ticket-specified direct construction (planning finding 3):
  `(op φ) a := ∑'_b M a b · φ b`, summable since `‖M‖ ≤ 1` and `φ` vanishes
  cofinitely; `‖op φ‖ ≤ ‖φ‖`; output vanishes cofinitely by splitting columns at a
  level `N` (small tail) and using row decay below it.
  - Source: [LWX, Thm 3.16 proof] p. 22 (well-definedness paragraph) — the operator
    is the matrix; our construction realises it on `c(ι×ℕ, ·)`.
  - Attacks: [discharge] `exists_coeffEquiv` REJECTED (IsTate — finding 3);
    [linearity/continuity] `LinearMap.mkContinuous` with bound 1; [matrixCoeff_op]
    `single`-evaluation collapses the tsum to one term ✓.
  - Sizing: ~120 LOC.

#### E — the two-sided bound (`PhD/TateFredholm/TwoSidedBound.lean`)

- **E1** (leaves): `sum_sub_le_sum_sub_comp`, `norm_minor_le_pow_sub`
  (TwoSidedBound.lean:50–63).
  - Source: [LWX, Thm 3.16 proof] p. 22 — "We now conjugate the matrix `P` by the
    infinite diagonal matrix whose diagonal entries are `1,…,1, T,…,T, T²,…` …
    `P′_{m,n} ∈ 𝔪^{max{⌊m/t⌋−⌊n/pt⌋,0}} · T^{⌊n/t⌋−⌊m/t⌋}Λ^{>1/p} ⊆
    T^{max{⌊n/t⌋−⌊n/pt⌋, ⌊n/t⌋−⌊m/t⌋}}Λ^{>1/p}`. In particular, the entries of `P′`
    in the `n`-th column all lie in `T^{⌊n/t⌋−⌊n/pt⌋}Λ^{>1/p}`."
  - Lean ↔ source: minor-level reading (see the Faithfulness note above): the
    diagonal-conjugation exponent bookkeeping is `Σ_S w'∘π = Σ_S w'` inside each
    Leibniz monomial. Hadamard mechanics mirror `TateFredholm.Slopes`'s
    `norm_det_le_pow_of_row_bound` (project pattern, verified).
  - Attacks: [composition] could children hold and the parent fail through the ℕ-sub
    truncations? Checked orders: `Σ max(w−w'∘π, 0) ≥ max(Σw − Σw'∘π, 0) =
    max(Σw − Σw', 0)` — the permutation identity is applied *before* un-truncating ✓;
    [edge] `S = ∅` (`minor = det of empty = 1`, bound `σ⁰ = 1` ✓ with `‖1‖ = 1` —
    `NormOneClass` used, present in hypotheses); `w' ≡ 0` degenerates to the row
    bound ✓ (sanity against `Slopes.lean`).
  - Sizing: ~90 LOC (pattern exists).
- **E2** (leaves): `summable_minor_of_two_sided`, `norm_charCoeff_le_pow_two_sided`
  (TwoSidedBound.lean:65–96).
  - Source: [LWX, Thm 3.16 proof] p. 22 — "modulo `𝔪^r_Λ` for each `r ∈ N`, the
    infinite matrix is strict upper triangular except the first
    `⌊ptr/(p−1)⌋ × ⌊ptr/(p−1)⌋`-minor … This implies that `Char(P) ∈ ΛJXK` is well
    defined."
  - Lean ↔ source: the same finiteness (`w − w'` cofinitely large ⟹ finitely many
    `S` below any weight bar) drives summability in the normed reading; then
    `norm_tsum_le_iSup` (verified, Tate.lean) + E1 gives the coefficient bound. No
    `IsTate` anywhere (checked: `charCoeff`/`minor` defs are norm-free —
    Fredholm.lean:33/148).
  - Attacks: [hypothesis-strength] is `Tendsto … cofinite atTop` the right growth
    condition? For the application `w−w' = m − ⌊m/p⌋ → ∞` on `ι × ℕ` with finite `ι`
    ✓; a constant-weight counterexample (`w = w'`) makes the family non-summable in
    general — and indeed then the hypothesis fails ✓ not over-general; [edge]
    `n = 0` (`charCoeff 0 = 1`, `f 0 ≤ 0` forces `f 0 = 0`, bound `= 1` ✓).
  - Sizing: ~110 LOC.
- **E3** (leaf): `sum_comp_div_le_sum_monotone` (TwoSidedBound.lean:88).
  - Source: [LWX, Thm 3.16] p. 22 (the definition of `λ` via increments) — the
    minimum-filling count; proof pattern = `TateFredholm.sum_div_le_sum_block`
    (project, verified: same induction "peel the maximal second coordinate").
  - Attacks: [edge] `v` constant (both sides equal `n·v(0)`… LHS `Σ v(k/t)` = `n·c`,
    RHS `≥ n·c` ✓); `ι` empty with `n > 0` — impossible (`S` nonempty forces
    inhabited ι, same guard as the existing lemma ✓); [subsumption sanity] `v = id`
    recovers `sum_div_le_sum_block` verbatim ✓.
  - Sizing: ~50 LOC.

#### F — assembly (`PhD/LWX/Halo.lean`), R1 part

- **F1** (leaves): `lwxLambda`, `lwxLambda_succ`, `monotone_sub_div`,
  `lwxLambda_eq_sum_comp` (Halo.lean:41–53).
  - Source: [LWX, Thm 3.16] p. 22 — "where `λ(0) = 0, λ(1), …` is a sequence of
    integers determined by `λ(i + 1) − λ(i) = ⌊i/t⌋ − ⌊i/pt⌋`."
  - Discharges: `Finset.sum_range_succ`; `Nat.div_div_eq_div_mul` (verified in
    `Data/Nat/Basic.lean` usage) for `⌊⌊k/t⌋/p⌋ = ⌊k/(pt)⌋`; monotonicity of
    `m − ⌊m/p⌋` by `omega`-adjacent case analysis.
  - Attacks: [edge] `t = 0` (division by zero conventions: `k/0 = 0`, λ ≡ 0 — the
    degenerate `ι = ∅` never occurs with an inhabited class set, and no lemma
    divides by the hypothesis; junk-safe); `p*t` vs `t*p` order fixed to match
    `div_div`; [monotonicity check] increments non-decreasing: crossing a multiple
    of `pt` changes both floors (+1, +1), net 0; crossing a `t`-multiple only: +1 ✓.
- **F2** (leaves): `summable_minor_upOp`, `norm_charCoeff_upOp_le`,
  `exists_charCoeff_upOp_eq_T_pow_mul`, `norm_coeff_charCoeff_upOp_le`
  (Halo.lean:59–84). **MILESTONE (Theorem 3.16).**
  - Source: [LWX, Theorem 3.16] pp. 21–22 — statement (3.16.1):
    "`c_n ∈ T^{λ(n)} · Λ^{>1/p}` for `n ∈ Z≥0`".
  - Composition: E2 with `w(i,m) = m`, `w'(j,n) = ⌊n/p⌋` (bounds from D5), `f = λ`
    justified by E3 at `v(m) = m − ⌊m/p⌋` + F1's floor identity; then A4 converts
    norm ⇒ `T`-power, and `norm_le_zpow_iff` gives the coefficientwise reading
    ([LWX, Cor 3.18 proof] first display: "`v(b_{n,m}) ≥ max{λ(n) − m, 0}`").
  - Attacks: [composition] the weight-sum chain re-derived by hand at `n = t = 1`,
    `p = 3`: `λ(1) = 0` ✓ (`c_1` = trace, entries `m = n = 0` bound `p⁰`);
    at `n = t+1`: first nontrivial λ ✓; [index flattening] the source's
    `⌊N/t⌋`-flattening vs our `ι × ℕ` blocks: E3 needs only the *count* `|ι| = t`
    per weight level — no ordering of `ι` is ever chosen, strictly less structure
    than the source's flattening, same minimum ✓.
- (F3–F5 belong to R2 below; G to R3.)

---

## Result R2 — Corollary 3.18 (lower-bound polygon at every halo weight)

### Source proof read (Step 1)

[LWX, Cor 3.18] p. 23, six lines: coefficients of `Λ^{>1/p}`-elements satisfy
`v(d_m) ≥ max(0, −m)`; combined with (3.16.1), `v(b_{n,m}) ≥ max{λ(n) − m, 0}`; then
display (3.18.1): "`v(b_{n,m}T^m) ≥ max{λ(n) − m, 0} + mv(T) ≥ λ(n)v(T)`, with the
second equality holding if and only if `m = λ(n)`"; conclusion: "the Newton polygon of
`Σ c_n(T)X^n` always lies above the polygon with vertices `(n, λ(n)v(T))`".

Prose (ours): specialise coefficientwise (`specialize`), bound each term of the tsum
by (3.18.1)'s computation (leaf A13 = `norm_specialize_le`), get
`v(c_n(T₀)) ≥ λ(n)·v(T₀)` (F4); anchor at `c₀ = 1` and assemble the polygon statement
with `ofSlopes` exactly as `QMF.Weight.isBelow_newtonPolygon_heckeCharPowerSeries`
does (project pattern, verified at `Weight/Slopes.lean:142`).

### Leaves

- **A13** (leaves, in HaloRing): `specialize`, `summable_specialize`,
  `norm_specialize_le`, `specialize_one`.
  - Source quote: (3.18.1), above.
  - Lean ↔ source: `norm_specialize_le` is (3.18.1) summed: hypothesis
    `‖f‖ ≤ p^{−k}`, conclusion `‖Σψ(f_j)T₀^j‖ ≤ ‖T₀‖^k`. Termwise:
    `v(f_j) + j·v(T₀) ≥ max(k−j,0) + j·v(T₀) ≥ k·v(T₀)` using `0 < v(T₀) < 1` on
    the two branches (`j ≥ k`: `j·v ≥ k·v`; `j < k`: `(k−j)·1 + j·v ≥ (k−j)·v + j·v`).
  - Attacks: [edge] `j < 0` terms: `v(f_j) ≥ −j` makes `v(f_jT₀^j) ≥ −j(1 − v) > 0`
    ✓ (the halo condition `v < 1` is exactly what kills the left tail — and the
    attack "what if `‖T₀‖ ≤ p⁻¹`" correctly breaks it, matching the source's strict
    `|T| > 1/p`); [hypothesis] `hψ` isometric — needed for termwise valuations,
    supplied by any completion embedding; [summability] geometric tails both ways ✓.
  - Sizing: source 6 lines; ~110 LOC.
- **F4** (leaves): `specCharSeries`, `norm_specCharSeries_coeff_le`,
  `specCharSeries_coeff_zero` (Halo.lean:91–107).
  - Composition of F2 + A13; anchor via `charCoeff_zero` (library, verified) +
    `specialize_one`.
  - Attacks: [edge] `n = 0` (`λ(0) = 0`, bound `= 1` ✓ consistent with coeff `= 1`).
- **F5** (leaves): `lwxSlopes`, `monotone_lwxSlopes`,
  `isBelow_newtonPolygon_specCharSeries` (Halo.lean:111–126). **MILESTONE
  (Corollary 3.18).**
  - Source: [LWX, Cor 3.18] p. 23 — "the Newton polygon of `Σ_{n≥0} c_n(T)X^n`
    always lies above the polygon with vertices `(n, λ(n)v(T))` for all `n ≥ 0`."
  - Lean ↔ source: `ofSlopes` with unit slopes `(⌊k/t⌋−⌊k/pt⌋)·(−log‖T₀‖)` has
    vertex heights `Σ_{k<n} = λ(n)·v(T₀)` ✓; `IsBelow` against
    `newtonPolygon₀OfPowerSeries negLogNorm` is the repo's exact phrasing of "lies
    above" (project pattern: `Weight/Slopes.lean:142–166` assembly, reused
    step-for-step with the new slope function).
  - Attacks: [orientation] `IsBelow` direction double-checked against the model
    statement (the *witness* polygon is below the *true* one ✓ same as A5
    milestone); [edge] all `c_n(T₀) = 0` beyond `n = 0` — polygon has a final ray;
    `ofSlopes`-vs-ray semantics already handled by `isNewtonPolygonOf_ofSlopes`'s
    hypotheses (verified exported); [monotone] increments ≥ 0 since
    `−log‖T₀‖ > 0` at `‖T₀‖ < 1` ✓.
  - Sizing: model proof is ~25 lines; ~60 LOC.

---

## Result R3 — the quaternionic shape ([LWX, Prop 3.1], local half)

### Source proof read (Step 1)

[LWX, Prop 3.1] p. 16, proof reproduced from [WXZ14+, Prop 4.4]: write
`γ_i v_j^{−1} = δ_{i,j}^{−1} γ_{λ_{i,j}} u_{i,j}`, get
`(U_pφ)(γ_i) = Σ_j φ(γ_{λ_{i,j}})‖_{δ_{i,j,p}}` and check
"`δ_{i,j,p} = u_{i,j,p} v_j ∈ Iw_q (p 0; 0 1) Iw_q ⊆ (pZp Zp; qZp Z×p)`."
Footnote 3 (p. 13): "the assumption `γ_{i,p} = 1` is not essentially needed to prove
Proposition 3.1(3)". §2.5: "for example with `v_j = (p 0; jq 1)`".

Scope decision (recorded in plan.md): Tier 1 formalises the *local* content — the
shape closure `u·v_j ∈ (pZp, Zp; pZp, Z×p)` for Iwahori-shaped `u`, and the assembly
of a `UpDatum` from class-set coset data. The adelic Prop 3.1 (deriving that data from
`heckeOperatorSlash_apply_rep` at a concrete level, and that the resulting matrix *is*
`U_p` on the integral model) is part of the deferred model seam.

### Leaves

- **G1** (leaves): `iwahoriRep`, `exists_localMat_iwahori_mul`, `UpDatum.ofCosets`
  (Halo.lean:130–151).
  - Source quotes: as above (`v_j` display + the shape-inclusion display).
  - Lean ↔ source: `u·v_j` computed entrywise:
    `(u·v_j)₀₀ = u₀₀p + u₀₁jp ∈ pℤ_p` ✓, `(u·v_j)₁₀ = u₁₀p + u₁₁jp ∈ pℤ_p` ✓,
    `(u·v_j)₁₁ = u₁₁ ∈ ℤ_p^×` ✓, `(u·v_j)₀₁ = u₀₁` free ✓ — exactly the source's
    inclusion, with the Iwahori hypotheses (`u₀₀, u₁₁` units, `v(u₁₀) ≥ 1`) as
    stated for `Iw_q`.
  - Attacks: [edge] `j = 0` (`v_0 = diag(p,1)` ✓); [hypothesis] is `u₀₀`-unit
    needed? Not for the four checks above (only `u₁₁`) — kept because `Iw_q`
    membership supplies it and dropping it would misrepresent the source's set; a
    note for `/cleanup` to consider weakening; [column bound] `(u·v_j)₁₁` unit
    requires `u₁₁` unit and nothing else ✓.
  - Sizing: source 2 lines; ~70 LOC.

---

## API gaps summary

- **AG1** (Teichmüller + qlog): tranche B; leaves B1–B5 above, all with
  decompositions grounded in standard estimates; no external blockers.
- **AG2** (`HaloInt`): tranche A; the only genuinely bespoke construction. Its
  riskiest leaf (A1's `mul_assoc` via ℤ-indexed Fubini) has a named mathlib toolkit
  (`Summable.tsum_prod`-family + `tsum_mul_tsum_of_summable_norm`) but no single
  off-the-shelf lemma; priced accordingly.

## Confidence gate (Step 5) — status

1. Every leaf discharged from mathlib (verified names), project code (cited
   file:line), or sits in AG1/AG2 with its own sub-tree ✓
2. Skeleton compiles, sorries only (95 across six files) ✓
3. Verbatim quotes + match paragraphs per leaf cluster ✓
4. Adversarial pass run; three planning-time attacks succeeded and were absorbed
   into the design; one statement-level fix queued at C7 (`nat_ineq_3_13_2`
   hypotheses) and recorded in its ticket ✓
5. Prior-B2 log consulted; clean ✓
6. Tree mirrors [LWX]'s §3 proof structure (each internal node cites the page of the
   source's own proof; the one deliberate reading — conjugation at minor level — is
   flagged with its justification and the exact source displays it implements) ✓
7. Statements single-conclusion (multi-part statements split: e.g. Thm 3.16 = norm
   form + T-power form + coefficient form as three leaves; Prop 3.14 = per-coefficient
   + packaged) ✓

Gate: **PASS**, with C7's hypothesis fix to be applied as the first action of ticket
C7 (recorded there; the fix does not change the tree).

---
---

# Revision 2026-09-03 — tranche H (the integral model), and the `M₁`-first restructure

User-approved unification with the QMF slash layer, after verifying that
`PhD/QMF/Slash/HeckeMonoid.lean` (variables `[Semiring R] [Module R A]
[SMulSlashClass R Δ' A]`, line 47–50) and `Slash/HeckeMatrix.lean` (line 35; incl.
`heckeOperatorSlash_apply_rep` :57 and `bijective_evalAtRepsSlash` :181) are
**ring-generic** — so [LWX, (2.11.1)] and the Prop 3.1 display are reused, not
re-proved. Skeleton extended (`PhD/LWX/IntegralModel.lean`, 12 new sorried
declaration groups; `UpMatrix.lean`/`Halo.lean` adjusted); `lake build` re-verified
clean, sorries only, 2026-09-03.

## Planning-time adversarial finding 4 (attack that SUCCEEDED)

**Stability needs Prop 3.14(2), not just (1).** The rescaled model's stability under
`M₁` ([LWX, §5.4]: "We claim that this subspace is stable under the action of the
monoid `M₁`") requires the entry bound at a *general* `δ ∈ M₁` — exponent `m − n` —
which case (1) (exponent `m − ⌊n/p⌋`, only for the `U_p`-shape) does not supply for
matrices with `a ∉ pℤ_p` (e.g. `δ = 1`, whose entries are deltas: the (m,n)-entry
`δ_{mn}` satisfies `m − n = 0` but not `m − ⌊n/p⌋ > 0` at `n < m ≤ p·n`… checked at
`(m,n) = (1,1)`: identity entry `= 1`, `m − ⌊n/p⌋ = 1` would demand norm `≤ p⁻¹` —
**false**). Hence the restructure below.

## D-tranche restructure (statements changed; tree shape unchanged)

- `LocalMat` is now [LWX, (2.3.3)]'s `M₁` in record form — the `ha` field moved to
  the refinement `IsUpShape` ("Each `δp` appearing above belongs to
  `(pZp Zp; qZp Z×p)`" [LWX, Prop 3.1(3)] = `IsUpShape`; membership in `M₁` needs
  only `q|c, p∤d, ad−bc ≠ 0`).
- **D1b** (new leaf): `exists_hasSum_mobiusFun_logShape` (UpMatrix.lean:76).
  - Source (verbatim, [LWX, Prop 3.14 proof] p. 21): "In case (2), note that `f(z)`
    is of the form considered in Lemma 3.13."
  - Lean ↔ source: for `δ ∈ M₁` only `c` carries `p`; the geometric-expansion
    coefficients have `v ≥ k − 1 ≥ (k−1) − v(k)`, i.e. `IsLogShape` — the same
    computation as D1 with the weaker input.
  - Attacks: [edge] `δ = 1` (`f = z`: `A_1 = 1`, `‖A_1‖·‖1‖ = 1 ≤ p⁰` ✓); [drift]
    the source treats case (2) in one line — our leaf is its expansion; [discharge]
    same toolkit as D1.
- **D3-M1** (new leaves): `norm_entryCoeff_le_M1`, `norm_entry_le_M1`
  (UpMatrix.lean:139–146).
  - Source (verbatim, [LWX, Prop 3.14(2)] p. 21): "When `δp = (a b; c d) ∈ M₁`, the
    coefficient `P_{m,n}(δp)` belongs to `𝔪_Λ^{max{m−n,0}}`."
  - Composition: Lemma 3.13 on `binom(f, n)` (via D1b) replaces Lemma 3.12; the rest
    of the D3 chain is identical. Attacks: [edge] `δ = 1`, `(m,n) = (1,1)` — bound
    `p⁰` ✓ (this is finding 4's witness, now on the correct side); [composition] the
    two cases share every other step — no fork drift.
- `UpDatum` gains the field `hshape` (every datum matrix has the `U_p`-shape), and
  `exists_localMat_iwahori_mul` (G1) concludes `IsUpShape` as its first conjunct.

## Tranche H leaves (`PhD/LWX/IntegralModel.lean`)

- **H1** (leaves): `oneAddTPow` (+ bound field, `coeff_`, `_zero`, `_add`),
  `logQuot`/`coe_logQuot`, `univChar` (+ `_one`, `_mul`, `norm_le`)
  (IntegralModel.lean:55–91).
  - Source ([LWX, Notation 2.1] p. 8, verbatim): "where `T` corresponds to
    `[exp(q)] − 1`. … `[−] : Z×p → Λ×` is the *universal character* of `Z×p`." And
    the splitting quote (decomposition B1).
  - Lean ↔ source: per-ω the universal character is `[a] = ω(ā)·(1+T)^{ℓ⟨a⟩}` with
    `ℓ = (1/q)log`; `(1+T)^s := ∑ Ring.choose s k·Tᵏ` (coefficients integral —
    `BinomialRing ℤ_[p]`), multiplicativity = Chu–Vandermonde `Ring.add_choose_eq`
    (verified, Binomial.lean:519) + `teichmuller_mul` + `qlog_mul` (B1/B4).
  - Attacks: [edge] `a = 1` (`ℓ = 0`, `oneAddTPow 0 = 1` ✓); [hypothesis] `univChar`
    lands in the ring, unit-ness comes via `univChar_mul` with `a⁻¹` — no separate
    inverse construction needed; [discharge] `Ring.choose` norm `≤ 1` is automatic
    (values in `ℤ_[p]`) so the `oneAddTPow` bound field is the `j < 0` branch only ✓.
  - Sizing: source 3 lines; ~140 LOC.
- **H2** (leaves): `M1` (mul/one closure), `M1.toLocalMat` + 4 coordinate lemmas,
  `LocalMat.denUnit`, `cfunSlash` (continuity field), `cfunSlashAction`
  (zero/one/**mul**/add), `cfunSMulSlash` (IntegralModel.lean:100–153).
  - Source ([LWX, (2.3.2)–(2.3.3)] p. 10, verbatim): "`h‖χ_{(a b; c d)}(z) =
    … = χ(cz + d)h((az + b)/(cz + d))`. One checks that this action extends to an
    action of the monoid `M₁ := {(a b; c d) ∈ M₂(Zp) | q|c, p ∤ d, and ad − bc ≠ 0}`."
  - Lean ↔ source: the cocycle `slash_mul` is the "one checks" — Möbius composition
    (`(cz+d)`-cocycle of denominators) + `univChar_mul`; closure of `M₁` mirrors
    `Sigma0'.mul_mem'` (project pattern, Slash/Sigma0.lean:43, norms for
    valuations).
  - Attacks: [composition] the cocycle at `g₁g₂` needs `den(g₁g₂, z) =
    den(g₁, möb g₂ z)·den(g₂, z)` — checked by 2×2 algebra (the classical automorphy
    identity), with unit-ness on both sides ✓; [edge] `g = 1` (`den = 1`,
    `univChar 1 = 1`, `möb = id` ✓); [hypothesis] `det ≠ 0` carried in `M₁` (source
    has it) though the action formula never divides by it — kept for source fidelity,
    noted for `/cleanup`; [Sigma0' seam] identification deferred (no `Valued ℚ_[p]`
    instance pinned) — recorded, harmless: nothing consumes it.
  - Sizing: source 4 lines + "one checks"; ~220 LOC (the cocycle is the bulk).
- **H3** (leaves): `mahlerEmbed` (+ `_apply`), `fwdDiff_mahlerEmbed`,
  `mahlerEmbed_injective` (IntegralModel.lean:159–171).
  - Source ([LWX, (5.4.1)] p. 34, verbatim): "`Ind^{Iwq}_{B(Zp)}([−]')^{mod} =
    ⊕̂_{n≥0} T^n Λ^{>1/p} · (z n)`."
  - Lean ↔ source: the completed direct sum on the basis `{Tⁿ binom(z,n)}` is the
    image of `c(ℕ, Λ^{>1/p})` under `a ↦ ∑ aₙTⁿ·binom(·,n)`; extraction
    `Δ̃^m(…)(0) = aₘTᵐ` needs only `fwdDiff_iter_eq_sum_shift` +
    `Ring.choose_natCast`-vanishing `binom(0,k) = δ_{k0}` (finite sums — **no Mahler
    theorem over `Λ^{>1/p}`**, a design point).
  - Attacks: [edge] `a = single` (embed = one basis function ✓); [convergence] terms
    `‖aₙTⁿ·binom(z,n)‖ ≤ ‖aₙ‖p^{−n}` — summable uniformly ⟹ continuity of the sum
    (`TateFredholm.summable_of_tendsto_cofinite` + uniform-limit continuity);
    [injectivity] via extraction + `T`-torsion-freeness (`norm_T_mul` ≠ 0 scaling) ✓.
  - Sizing: source 2 lines; ~150 LOC.
- **H4** (leaves): `cfunSlash_mahlerEmbed` (shared-witness existential — justified:
  the coefficient stream `b` is the witness both conjuncts describe),
  `seqSlashAction`, `mahlerEmbed_seqSlash`, `seqSlash_coeff`
  (IntegralModel.lean:173–214).
  - Source: [LWX, Prop 3.4] (quote in D3) — **promoted from definition to theorem**
    here — and [LWX, §5.4] p. 34 (verbatim): "We claim that this subspace is stable
    under the action of the monoid `M₁`. Indeed, by Proposition 3.14(2) … the
    `(m, n)`-entry of the infinite matrix has coefficients in
    `T^{max{0,n−m}}Λ^{>1/p}`."
  - Lean ↔ source: stability = D3-M1's bound makes `T^{−m}·(∑ₙ aₙTⁿP_{m,n})`
    integral; the transported action is well defined by `mahlerEmbed_injective`;
    `seqSlash_coeff` is the matrix reading the Hecke assembly consumes.
  - Attacks: [composition] transported `slash_mul` follows from injectivity +
    `cfunSlashAction.slash_mul` — no new analysis; [edge] `g = 1` (entries = deltas,
    `b = a` ✓ — finding 4's sanity case); [division worry] `T^m ∣ ·` extraction uses
    A4's `exists_T_pow_mul_of_norm_le`, no division operator ✓.
  - Sizing: source 6 lines; ~180 LOC.
- **H5** (leaves): `levelM1`, `intAutSlashAction` (def-hole: the `QMF.Slash`
  automorphic-action constructor at `θ`; ticket pins the exact declaration),
  `IntForms`, `intEvalAtReps` (mirror of Weight/Compact.lean:92 at `R = HaloInt p`),
  `intEvalAtReps_comm` (IntegralModel.lean:216–260).
  - Source ([LWX, §2.7] p. 12, verbatim): "Define the space of *integral p-adic
    automorphic forms* for `D` to be `S^D_int := {φ : D×\(D ⊗ Af)×/Kp →
    Ind^{Iwq}_{B(Zp)}([−]) | φ(xup) = φ(x)‖^{[−]}_{up}}`"; and [LWX, Prop 3.1]
    display (quote in R3): `(Upφ)(γi) = Σ φ(γ_{λi,j})‖_{δi,j,p}`.
  - Lean ↔ source: `IntForms = levelSubmoduleSlash` at the transported action —
    (2.11.1) is `bijective_evalAtRepsSlash` applied (ring-generic, verified);
    `intEvalAtReps_comm` takes Prop 3.1's display as hypothesis `hΦ` (discharged at
    instantiation by `heckeOperatorSlash_apply_rep`, already proved) and concludes
    the intertwining with `UpDatum.op` — the layering QMF's own
    `Weight/Compact.lean` uses for its transport.
  - Attacks: [circularity check] `hΦ` is *not* the conclusion: hypothesis = values
    at representatives (function-level display), conclusion = the block-model
    intertwining with the abstract matrix operator — the content is
    `seqSlash_coeff` + `blockIncl` bookkeeping; [edge] `Φ = 0` fails `hΦ` unless
    entries sum to zero — vacuous-instantiation attack fails ✓; [interface] `Φ`
    abstract linear (not `heckeOperatorSlash` itself) — deliberately, so the leaf
    doesn't repeat the Hecke finiteness plumbing; the instantiation lives with the
    future concrete-level application (plan.md, still-deferred item 3).
  - Sizing: model proof (Weight/Compact's transport) exists as pattern; ~200 LOC.

## Confidence gate — revision status

All seven conditions re-checked for the new/changed leaves: skeleton compiles
(sorries only, verified 2026-09-03); every new leaf has quote + match + attacks;
prior-B2 log re-consulted (no new matches); the tree still mirrors the source
([LWX] §2.3, §2.7, §5.4 added to the mirrored sections); single-conclusion check:
`cfunSlash_mahlerEmbed` is a documented shared-witness exception; H5's `IntForms`
def-hole and `intAutSlashAction` def-hole are definitions, not statements.
Gate: **PASS** (C7's queued fix unchanged).
