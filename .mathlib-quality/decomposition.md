# Decomposition — Martin's Weierstrass division & preparation (full generality)

## Skeleton location
Every lemma stated with `:= by sorry` (except definitional projections) in:
- `PhD/Martin/NormMulUnit.lean`
- `PhD/Martin/Distinguished.lean`
- `PhD/Martin/WeierstrassDivision.lean`
- `PhD/Martin/WeierstrassPrep.lean`

`lake build PhD.Martin.WeierstrassPrep` **passes** (2171 jobs, sorry warnings only, no
type errors) — verified 2026-07-28.

Source text with line locators: `.mathlib-quality/references/martin-sec1.3.txt`
(= [Mar16] §1.3, pp. 11–15; PDF alongside). All quotes below are from that file; the
pypdf extraction garbles some math symbols (`∥`→`∥`, subscripts inline) — quotes are
verbatim from the extraction, cross-checked against the PDF.

Prior-B2 log: `.mathlib-quality/b2_log.jsonl` is **empty (0 entries)** — no name or
shape match is possible for any leaf; consultation recorded once here for all leaves.

## Result R1: `weierstrassDivision_exists_of_isMulDistinguished` (+ norm identity, uniqueness) — [Mar16, Prop 1.27]

### Plain-English proof (transcribed from martin-sec1.3.txt:141–219)

Let `g` be `T`-distinguished of order `s` (Def 1.24: `g_s` a multiplicative unit,
`‖g_s‖rˢ = ‖g‖`, strict dominance above `s`). **(a) Norm identity first** (:147–158):
for ANY pair `(q, R)` with `f = gq + R`, `deg R < s`, we have
`‖f‖ = max(‖g‖‖q‖, ‖R‖)`: if `‖gq‖ ≠ ‖R‖` this is the ultrametric equality plus
Lemma 1.26(1); otherwise Lemma 1.26(2) locates the index `s + k₀` (`k₀` = greatest
achieving index of `q`) where the coefficient of `gq` has norm exactly `‖g_s‖‖q_{k₀}‖`;
since `deg R < s ≤ s + k₀`, that coefficient survives in `f`, giving `‖f‖ ≥ ‖g‖‖q‖`.
**(b) Uniqueness** (:159–161): subtract two decompositions and apply (a) to
`0 = g(q−q') + (R−R')`. **(c) Existence** (:162–219): truncate the divisor to
`g' := Σ_{m≤s} g_m T^m` (a polynomial with invertible leading coefficient `g_s`, of the
same norm, again `T`-distinguished of order `s`) and set
`κ := max_{m>s}(‖g_m‖r^m)/‖g‖ < 1` (replace by `1/2` if `0`); truncate `f` to `f'` with
`‖f − f'‖ ≤ κ‖f‖`; divide `f'` by `g'` Euclideanly [Lan02, 4.1.1]; the norm identity
applied to `g'` bounds the quotient (`‖q‖ ≤ ‖f‖/‖g‖`) and remainder; the error
`f − (gq + R) = (f − f') + (g' − g)q` has norm `≤ κ‖f‖`. This is the one-step statement
(1.11); iterating it produces Cauchy sequences `(q_i)`, `(R_i)` with
`‖f − (gq_i + R_i)‖ ≤ κ^i ‖f‖`, whose limits (completeness) solve the division.
Our packaging of the last step: (1.11) iterated says `f ∈ closure (divisionSet g s)`,
and the bounds from (a) make `divisionSet g s` closed — same argument, phrased through
the project's `divisionSet` machinery (see L16/L17 composition note).

### Source's sub-results, read in full
- Def 1.20 (:47), Lemma 1.21 (:50, proof :51–56), Remark 1.22 (:57–66)
- Def 1.24 (:95–98), Lemma 1.26 with proof (:110–140)
- Prop 1.27 with full proof (:141–219)

### Leaves

- **L1** (leaf): `IsNormMulUnit` def + `mul` + `isNormMulUnit_one`
  - Lean: `PhD/Martin/NormMulUnit.lean:25` (def), `:36` (mul), `:41` (one);
    projections `:30`, `:32` (definitional, proven).
  - Source: Def 1.20, martin-sec1.3.txt:47–49:
    > "Definition 1.20. An element u ∈ A is a multiplicative unit if u is invertible and
    > for all a ∈ A, ∥ua∥ = ∥u∥∥a∥. Note that if u and v are multiplicative units, so is uv."
  - Lean ↔ source: `IsUnit u ∧ ∀ a, ‖u * a‖ = ‖u‖ * ‖a‖` is the definition verbatim
    (left multiplication; Martin's ring is commutative, ours `NormedRing` for the def).
  - Discharge: `mul` by associativity + both hypotheses (`‖(uv)a‖ = ‖u‖‖va‖ = ‖u‖‖v‖‖a‖`,
    3 rewrites); `one` by `one_mul`, `norm_one`. Mathlib-only.
  - Attacks: [1] counterexample: none — the def is a definition; `mul` checked at
    u = v = 1 and u a zero-divisor-free unit. [2] edge: trivial ring — every element
    is a unit and all norms 0; `∀ a, 0 = 0` holds, def degenerate but consistent;
    `isNormMulUnit_one` needs `NormOneClass` which excludes the trivial ring — correct
    scoping. [3] hypothesis: left-only multiplicativity suffices for every downstream
    use (checked each: L9 diagonal `g_s * q_{k₀}`, L19 `g_s * q₀`, L21 `q₀⁻¹ * q_i` —
    all left). No hidden assumption. [5] discharge: `one_mul`, `norm_one` exist (core).
    Verdict: SURVIVED.
  - Prior-B2: log empty, no match.

- **L2** (leaf): Lemma 1.21 — `norm_coe_inv_units` (forward, `NormOneClass`),
  `isNormMulUnit_of_norm_coe_inv_units` (converse, no `NormOneClass`),
  `coe_inv_units`.
  - Lean: `NormMulUnit.lean:45`, `:50`, `:55`.
  - Source: martin-sec1.3.txt:50–56:
    > "Lemma 1.21. An element u ∈A is a multiplicative unit if and only if u ∈A∗ and
    > ∥u−1∥ = ∥u∥−1. Proof. If u is a multiplicative unit, 1 = ∥uu−1∥ = ∥u∥∥u−1∥, so
    > ∥u−1∥ = ∥u∥−1. Conversely … ∥a∥ = ∥u−1(ua)∥ ≤ ∥u−1∥∥ua∥ = ∥u∥−1∥ua∥. So
    > ∥ua∥ ≥ ∥u∥∥a∥. Since in any case the reverse inequality … holds, we conclude."
  - Lean ↔ source: split into the two directions plus the inverse-closure corollary;
    `Aˣ` supplies the inverse canonically.
  - Discharge: forward: `hu.norm_mul u⁻¹` + `Units.mul_inv` + `norm_one` + real-field
    algebra (`eq_inv_of_mul_eq_one_right`-style). Converse: as quoted, splitting on
    `‖u‖ = 0` (then both sides of `‖ua‖ = ‖u‖‖a‖` vanish by submultiplicativity).
  - Attacks: [1] negation search: none plausible. [2] edge `‖u‖ = 0` in the converse
    (possible only in degenerate rings): handled by the 0-case split — the source
    implicitly assumes `‖u‖ ≠ 0`; our proof plan covers it, statement stays true.
    [3] hypothesis-strength: forward genuinely needs `‖1‖ = 1` (`1 = ‖u u⁻¹‖` step);
    converse does NOT — we dropped `NormOneClass` there (improvement over a uniform
    hypothesis; verified the quoted proof uses only submultiplicativity). [4] drift:
    statement is the quote, split in two. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L3** (leaf): Remark 1.22 — `isNormMulUnit_one_add`.
  - Lean: `NormMulUnit.lean:60`.
  - Source: martin-sec1.3.txt:57–60:
    > "Remark 1.22. As a consequence, if u ∈ A and ∥u∥ < 1, then (1 + u) is a
    > multiplicative unit because ∥1 +u∥ = 1 = ∥ ∑ n≥0 (−u)n∥ = ∥(1 +u)−1∥"
  - Lean ↔ source: same statement; hypotheses `[IsUltrametricDist A] [NormOneClass A]
    [CompleteSpace A]` — the source's standing assumptions for §1.3 (":A will be an
    ultrametric complete normed ring", :43–44).
  - Discharge: invertibility: mathlib `Units.oneSub (-x)` (Analysis/Normed/Ring/Units,
    needs `CompleteSpace`); `‖1 + x‖ = 1` via `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
    (in mathlib, used at ForMathlib GaussExtension.lean:195); `‖(1+x)⁻¹‖ = 1` WITHOUT the
    series: `v := (1+x)⁻¹` satisfies `v = 1 − xv`, so `‖v‖ ≤ max(1, ‖x‖‖v‖)` forces
    `‖v‖ ≤ 1`, and `1 = ‖(1+x)v‖ ≤ ‖v‖`; close by L2 converse.
  - Attacks: [1] negation: no. [2] edge `x = 0`: `1 + 0 = 1`, `isNormMulUnit_one` ✓;
    edge `‖x‖ → 1⁻`: strictness needed for `norm_ne_norm` — hypothesis is strict ✓.
    [3] our proof avoids the source's tsum — composition re-derived and checked above
    (`v = 1 − xv` from `(1+x)v = 1`); this is a *proof simplification*, statement
    unchanged, so no source drift. [5] `Units.oneSub` verified present (grep, file
    header line 20 + usage line 50). Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L4** (leaf, bridge — no source): `IsUnit.isNormMulUnit` under `[NormMulClass A]`.
  - Lean: `NormMulUnit.lean:65`. Structural bridge to the project; not a source claim.
  - Discharge: `norm_mul` is an equality in `NormMulClass`; both fields immediate.
  - Attacks: [2] trivial ring is a `NormMulClass` (all norms 0)? Then `‖u*a‖ = 0 = ‖u‖‖a‖`
    ✓ holds. [3] no extra hypotheses. Verdict: SURVIVED.

- **L5** (leaf): `IsMulDistinguished` def + `toIsDistinguished` + `NormMulClass` iff.
  - Lean: `Distinguished.lean:35` (structure), `:46`, `:51`.
  - Source: Def 1.24, martin-sec1.3.txt:95–98:
    > "Definition 1.24. Let r >0 be a real number and s ∈ N. An element g = ∑ n≥0 gnTn
    > of A{r−1T } is called T -distinguished of order s if gs is a multiplicative unit,
    > ∥gs∥rs = ∥g∥ and for all n > s, ∥gn∥rn < ∥gs∥rs. Note that in that case, g is
    > necessarily a non zero element since gs ̸= 0."
  - Lean ↔ source: three fields = the three clauses, with `gaussNorm norm c f` the
    project's Gauss norm (defeq to `‖g‖` on `Restricted` via `norm_def`). Mirrors the
    field names of the project's `IsDistinguished` so proofs transport.
  - Discharge: `toIsDistinguished` = fields + `IsNormMulUnit.isUnit`; iff = L4 for `←`.
  - Attacks: [3] hypothesis-strength: is Martin's "strict above `s` only" faithfully
    kept (ties below allowed)? Yes — field `gaussTerm_lt` quantifies `s < t` only;
    tested against `g = X₀ + X₁`-style examples (tie at index 0, still distinguished).
    [4] drift-check against the project's `IsDistinguished` (Restricted/Distinguished.lean:38):
    identical except `IsUnit` → `IsNormMulUnit` — exactly the intended strengthening;
    over `NormMulClass` the iff restores equality of notions. [1] `lean_local_search`
    for contradicting lemmas: none (new predicate). Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L6** (leaf): `exists_greatest_achievesGaussNorm`.
  - Lean: `Distinguished.lean:64`.
  - Source: martin-sec1.3.txt:112–113 (inside Lemma 1.26):
    > "Let us denote by k0 the greatest rank such that ∥qk0∥rk0 = ∥q∥."
  - Lean ↔ source: existence of that greatest rank (the source uses it silently; the
    attaining set is nonempty and Gauss terms tend to 0, so it is finite-above).
  - Discharge: project `exists_coeff_ne_zero_norm_eq` (GaussNorm.lean:213, verified) +
    `isRestricted_iff'` tendsto-zero + `Nat` well-ordering on the (bounded-above)
    attaining set.
  - Attacks: [2] edge `q` a monomial (single attaining index): greatest = that index ✓;
    `q = 0` excluded by hypothesis (source also assumes `q ≠ 0`). [3] the `hkmax`
    conclusion is phrased `< ‖q‖` (not `< ‖q_{k₀}‖c^{k₀}`) — equal by the achieving
    equation, chosen for downstream convenience; no strengthening. [5] cited project
    lemmas exist at the greppen lines. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L7** (leaf): truncation bounds — `norm_toRestricted_trunc_le`,
  `exists_norm_sub_toRestricted_trunc_le`.
  - Lean: `Distinguished.lean:69`, `:75`.
  - Source: martin-sec1.3.txt:166–169:
    > "Next, let N ∈ N and let us set f′ := ∑ N k=0 fkTk. Let us assume that N is big
    > enough to satisfy ∥f −f′∥ ≤ κ∥f∥. In particular, ∥f′∥ = ∥f∥."
  - Lean ↔ source: `f' = toRestricted (trunc N f)`; the two lemmas give `‖f'‖ ≤ ‖f‖`
    (the source's "in particular" direction ≤; equality not needed downstream) and the
    "N big enough" existence for any `ε > 0`.
  - Discharge: `PowerSeries.coeff_trunc` (mathlib Trunc.lean:63) — coefficients agree
    below `N`, vanish above; norm as Gauss sup + tendsto-zero of Gauss terms.
  - Attacks: [2] edge `f = 0`: both trivial ✓; `ε ≥ ‖f‖`: `N = 0` works ✓. [3] we
    demand only `≤ ε`, not the source's `≤ κ‖f‖` — caller instantiates `ε := κ‖f‖`,
    which requires `κ‖f‖ > 0`: that's why L15's signature carries `0 < θ` (attack
    surfaced this; hypothesis added — see L15). [5] `coeff_trunc`, `degree_trunc_lt`
    verified by grep. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L8** (leaf): `isMulDistinguished_toRestricted_trunc`.
  - Lean: `Distinguished.lean:82`.
  - Source: martin-sec1.3.txt:162–165 and :173:
    > "Let us set g′ := ∑ s m=0 gmTm. In particular, ∥g∥ = ∥g′∥ because g is
    > T -distinguished of degree s." … "(because g′ is also T -distinguished of order s)"
  - Lean ↔ source: `g' = toRestricted (trunc (s+1) g)` (note `s+1`: mathlib `trunc N`
    keeps coefficients `< N`); conclusion exactly "g' is T-distinguished of order s".
  - Discharge: `coeff_trunc` (coefficient `s` preserved — `s < s + 1`), Gauss-norm of a
    truncation via L7's computation; strict dominance above `s` vacuous (coefficients 0,
    and `0 < ‖g_s‖cˢ` from the parent's `gaussTerm_lt` at `t = s+1`).
  - Attacks: [2] **off-by-one attack**: `trunc s` would DROP coefficient `s` (mathlib
    trunc keeps `m < N`) — the skeleton uses `trunc (s+1)` everywhere; verified
    against `coeff_trunc`'s guard `m < n`. [2'] edge `s = 0`: `g'` is the constant
    `g₀`, distinguished of order 0 ✓. [3] positivity `0 < ‖g_s‖cˢ`: derivable, no
    extra hypothesis needed (attack tried adding `Nontrivial A` — unnecessary, the
    strict field at `t = s+1` already forces it). Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L9** (leaf): **Lemma 1.26(2)** — `norm_coeff_add_mul_of_isMulDistinguished`.
  - Lean: `Distinguished.lean:90`.
  - Source: martin-sec1.3.txt:110–115 (statement):
    > "Lemma 1.26. Let g = ∑ … be T -distinguished of order s. (1) Then for all
    > q = ∑ …, ∥gq∥ = ∥g∥∥q∥. (2) Let us set gq = ∑ l∈N clTl, and let us assume that
    > q ̸= 0. Let us denote by k0 the greatest rank such that ∥qk0∥rk0 = ∥q∥. Then
    > ∥gq∥ = ∥cs+k0 ∥rs+k0 and ∥cs+k0 ∥ = ∥gs∥∥qk0∥."
    Proof (:116–140): cross terms with `k > k0` are strict by definition of `k0`;
    cross terms with `k < k0` have `m > s`, strict by distinguishedness; the diagonal
    `gs qk0` has norm `∥gs∥∥qk0∥` because `gs` is a multiplicative unit; conclude by
    the ultrametric sum equality.
  - Lean ↔ source: our statement is the second displayed equality
    `‖c_{s+k₀}‖ = ‖g_s‖‖q_{k₀}‖`, with `k₀` supplied by hypothesis (from L6); the
    first equality of (2) and part (1) are recovered in L10.
  - Discharge: adapt the project's `norm_coeff_mul_pow_eq_of_dominant`
    (WeierstrassDivision.lean:58) — same skeleton (`PowerSeries.coeff_mul` +
    `IsNonarchimedean.apply_sum_eq_of_lt`), with the two `norm_mul` uses replaced by
    `hg.isNormMulUnit_coeff.norm_mul` on the diagonal and submultiplicativity
    (`norm_mul_le`) on cross terms; cross-term strictness by Martin's two cases above.
  - Attacks: [1] falsity search — could a cross term TIE the diagonal at a general
    normed ring? The two cases cover every `(m,k) ≠ (s,k₀)` on the antidiagonal:
    `k > k₀` ⇒ `‖q_k‖r^k < ‖q_{k₀}‖r^{k₀}` (greatest), `k < k₀` ⇒ `m = s+k₀−k > s`
    ⇒ strict by `gaussTerm_lt`; both then multiply against `≤`-bounds on the other
    factor. Exhaustive. [2] edge `k₀ = 0`, `s = 0`, `q` monomial: all reduce to the
    diagonal only ✓. [3] `q ≠ 0` is carried implicitly by `hk`/`hkmax` (an achieving
    index exists only for `q ≠ 0` — for `q = 0`, `AchievesGaussNorm` would say
    `0 = 0`… attack pressed: if `q = 0` then `hk` holds trivially (`0*c^k = 0 = ‖0‖`)
    and the conclusion `‖0‖ = ‖g_s‖·0` holds too ✓ statement is true even at `q = 0`).
    [4] drift: hypothesis uses `‖q‖` for `gaussNorm` — equal by `norm_def`, `rfl`-level.
    [5] `IsNonarchimedean.apply_sum_eq_of_lt` — used at WeierstrassDivision.lean:65,
    exists ✓. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L10** (leaf): **Lemma 1.26(1)** — `norm_mul_of_isMulDistinguished`.
  - Lean: `Distinguished.lean:97`.
  - Source: as L9, part (1); proof :116–117 ("First, without any hypothesis, it is
    true that (1.3) ∥gq∥ ≤ ∥g∥∥q∥") and :138–140 ("Finally we obtain that
    ∥gq∥ ≥ ∥gs∥rs∥qk0 ∥rk0 = ∥q∥∥g∥, which with (1.3) ends the proof").
  - Discharge: `≤` is the `NormedRing` axiom on `Restricted`; `≥` from L9 via
    `norm_coeff_mul_pow_le` at index `s+k₀` and the achieving equations; `q = 0` case
    separate (both sides 0). Uses L6 to obtain `k₀`.
  - Attacks: [2] `q = 0` ✓ handled; `g` with ties below `s` (the crucial regime):
    e.g. `g = T + a`, `‖a‖r⁰ = ‖1‖r` — L9's argument never compares against index-
    below-`s` terms of `g` on the diagonal, only cross-terms with `k < k₀` which are
    strict via `m > s`. Re-derived by hand for `g = T + a`, `q = T + b`: the `(s+k₀)`
    = 2 coefficient is `1·1`; cross terms at index 2: none other. ✓ [3] could (1) hold
    with `IsUnit` only (drop multiplicativity)? No: `A = K⟨X⟩` at radius 1, `g = c`
    a constant unit with `‖c‖‖c⁻¹‖ > 1` gives `‖c·(c⁻¹)‖ = ‖1‖ = 1 < ‖c‖‖c⁻¹‖` —
    the mult-unit hypothesis is necessary. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L11** (leaf): norm identity (1.8) + bounds — `max_norm_le_…`, `norm_eq_max_…`,
  `norm_q_le_…`, `norm_toRestricted_le_…`.
  - Lean: `WeierstrassDivision.lean:33`, `:40`, `:46`, `:52`.
  - Source: Prop 1.27 statement + first proof part, martin-sec1.3.txt:141–158:
    > "Moreover (1.8) ∥f ∥ = max(∥g∥∥q∥, ∥R∥). Proof. First, let us show that if a
    > couple (q,R ) satisfies (1.7), then it must satisfy the equality (1.8). Because
    > of the ultrametric inequality, ∥f ∥ ≤ max(∥g∥∥q∥, ∥R∥). For the reverse
    > inequality, we distinguish two cases. If ∥gq∥ ̸= ∥R∥ … according to lemma 1.26.
    > Otherwise … We get ∥gq∥ = ∥cs+k0 ∥rs+k0 . Since R is a polynomial of degree d
    > with d <s … the coefficient fs+k0 of f is cs+k0 , hence ∥f ∥ ≥ ∥cs+k0∥rs+k0 = ∥g∥∥q∥."
  - Lean ↔ source: `max_norm_le` is the `≥` direction (the mathematical content);
    `norm_eq_max` adds the ultrametric `≤`; the two bounds are the corollaries Martin
    reads off (:174–176 uses them for the Euclidean quotient).
  - Discharge: adapt the project's `max_le_norm_of_eq_mul_add`
    (WeierstrassDivision.lean:79) line-by-line, replacing its two `norm_mul` rewrites
    by L10 and its dominant-pair peak by L6+L9 (the existing proof's
    `exists_achievesGaussNorm_dominant_max` route can be kept for the peak index or
    swapped for Martin's `k₀` route — ticket sketch fixes the latter, matching the
    source). Sub-case `q = 0` as in the existing proof.
  - Attacks: [1] the classic falsity risk — `‖f‖ ≥ ‖R‖` when `‖gq‖ = ‖R‖` with
    cancellation: killed exactly by the surviving coefficient at `s+k₀ ≥ s > deg R`…
    attack pressed on `k₀` minimal vs maximal: survival NEEDS `k₀` (greatest), since a
    smaller achieving index could collide with `R`'s support only if `s+k < s` —
    impossible anyway; but the CROSS-TERM argument needs greatest. Consistent. [2]
    edges: `q = 0` (then `f = R`, max = `‖R‖` ✓), `R = 0`, `s = 0` (then `R = 0`
    forced by `degree < 0`) ✓. [4] drift: none, statement is (1.8) split. Verdict:
    SURVIVED.
  - Prior-B2: log empty.

- **L12** (leaf): uniqueness — `weierstrassDivision_q_unique_…`, `_r_unique_…`.
  - Lean: `WeierstrassDivision.lean:59`, `:67`.
  - Source: martin-sec1.3.txt:159–161:
    > "From this we can conclude that the couple (q,R ) is unique because if f =gq′ +R′
    > is another decomposition, we have 0 = g(q −q′) + (R −R′) and since ∥g∥ ̸= 0,
    > ∥q −q′∥ = ∥R −R′∥ = 0, i.e. R =R′ and q =q′."
  - Discharge: verbatim the project's `weierstrassDivision_q_unique`/`_r_unique`
    proofs (WeierstrassDivision.lean:125/:140) with the Martin bounds L11;
    `Polynomial.toRestricted_injective` for `r`.
  - Attacks: [2] `s = 0`: `r₁ = r₂ = 0` ✓. [3] completeness-free ✓ (source proves
    uniqueness before invoking completeness — matched). [5] `toRestricted_injective`
    exists (used at project WeierstrassDivision.lean:147). Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L13** (leaf): `Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff`.
  - Lean: `WeierstrassDivision.lean:77`.
  - Source: martin-sec1.3.txt:170–173:
    > "By definition and hypothesis, g′ ∈ A[T ] is of degree s and possesses an
    > invertible dominant coefficient, which is gs. Hence in A[T ], one can carry out
    > euclidean division by g′ [Lan02, 4.1.1], which gives f ′ =g′q +R, with
    > R ∈As−1[T ] and q ∈A[T ]."
  - Lean ↔ source: stated for any `CommRing` + `Nontrivial`, divisor with `IsUnit
    leadingCoeff` — precisely Lang's IV.1.1 generality. Purely algebraic (no norms).
  - Discharge: search mathlib first (candidate names around `Polynomial.divByMonic`);
    fallback proof: `h := C u.unit⁻¹ * g₀` is monic (`monic_C_mul_of_mul_leadingCoeff_eq_one`,
    Monic.lean:60, verified), divide `f₀ %ₘ h` / `f₀ /ₘ h`
    (`modByMonic_add_div` Div.lean:259, `degree_modByMonic_lt` Div.lean:147, both
    verified), rearrange by commutativity, `degree h = degree g₀` via unit scaling.
  - Attacks: [2] **trivial-ring counterexample found and fixed**: with `R` trivial and
    `g₀ = 0`, `leadingCoeff = 0` is a unit but `r.degree < ⊥` is unsatisfiable — the
    statement is FALSE without `[Nontrivial R]`; hypothesis added to the skeleton.
    (This is the recorded catch of the adversarial pass.) [2'] edge `deg g₀ = 0`
    (unit constant): `r = 0`, `degree ⊥ < 0` ✓ (`WithBot`: `⊥ < 0` holds). [5]
    all three mathlib lemmas verified by grep at the cited lines. Verdict: SURVIVED
    (after fix).
  - Prior-B2: log empty.

- **L14** (leaf): `exists_lt_one_norm_sub_toRestricted_trunc_le_of_isMulDistinguished`.
  - Lean: `WeierstrassDivision.lean:85`.
  - Source: martin-sec1.3.txt:163–166:
    > "Let us set κ := max m>s (∥gm∥rm) / ∥gs∥rs … Since g is T -distinguished of
    > order s, κ <1. Actually, if κ = 0 (which would mean that g = g′), replace κ by
    > 1/2. In any case ∥g −g′∥ ≤ κ∥g∥ and κ ∈]0, 1[."
  - Lean ↔ source: exactly the quoted conclusion (`0 < θ < 1`, `‖g − g'‖ ≤ θ‖g‖`).
  - Discharge: the tail-sup is attained or 0 (Gauss terms → 0); strictness above `s`
    from `gaussTerm_lt`; `max · (1/2)` handles the 0 case. Same skeleton as project's
    `exists_lt_one_forall_norm_coeff_mul_pow_le` (WeierstrassDivision.lean:170) whose
    tendsto argument (`exists_pos_lt_forall_le_of_tendsto_zero`, :148 — private, small,
    re-derive or inline) restricts to `t > s` instead of `t ≠ s`.
  - Attacks: [2] `g` polynomial (tail empty): κ = 0 branch → 1/2 ✓ (source's own
    fix); `s = 0` ✓. [3] why `0 < θ` and not just `θ < 1`: needed by L15's use of L7
    with `ε := θ‖f‖` — positivity attack from L7 propagated here, satisfied by the
    `1/2` floor. [4] drift: `‖g−g'‖ ≤ κ‖g‖` is literally quoted. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L15** (leaf): one-step (1.11) — `exists_approx_div_of_isMulDistinguished`.
  - Lean: `WeierstrassDivision.lean:92`.
  - Source: martin-sec1.3.txt:174–186:
    > "We can then apply the norm equality (1.8) … (because g′ is also T -distinguished
    > of order s): ∥f ′∥ = max(∥g′∥∥q∥, ∥R∥). In particular ∥q∥ ≤ ∥f ′∥/∥g′∥ = ∥f ∥/∥g∥ …
    > Moreover ∥R∥ ≤ ∥f ′∥ = ∥f ∥. Thus … f =g′q +R + (f −f ′) + … h :=f −f ′ + (g′ −g)q
    > =f − (gq +R), … we obtain that ∥h∥ ≤ κ∥f ∥. To sum up, we have found some
    > κ ∈]0, 1[ such that (1.11) ∀f …, ∃q′ …, ∃R′ … such that ∥f − (gq ′ +R′)∥ ≤ κ∥f ∥."
  - Lean ↔ source: statement (1.11) verbatim, plus the quotient bound `‖q‖ ≤ ‖g‖⁻¹‖f‖`
    that the source derives en route (needed by L16's Cauchy bound and L17).
  - Discharge: `f = 0` trivial; else L7 (`ε := θ‖f‖ > 0`), L13 on `trunc` polynomials,
    L8 + L11 for the bounds on the polynomial division (note `‖g'‖ = ‖g‖` from L8's
    Gauss-norm field), error = ultrametric max of the two `≤ θ‖f‖` terms; `‖(g'−g)q‖ ≤
    ‖g'−g‖‖q‖` is `NormedRing` submultiplicativity.
  - Attacks: [2] `f = 0` ✓ (`q = R = 0`); `f` already a polynomial below `s` (`q = 0,
    R = f`, error 0) ✓ subsumed by the general route. [3] positivity of `θ‖f‖`
    (the L7 instantiation) — this is where `hθ0 : 0 < θ` earns its place (recorded
    fix). [4] drift: source's `‖q‖ ≤ ‖f‖/‖g‖` = ours via `le_inv_mul_iff₀`
    (‖g‖ > 0 from distinguishedness). Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L16** (leaf): `mem_closure_divisionSet_of_isMulDistinguished`.
  - Lean: `WeierstrassDivision.lean:103`.
  - Source: martin-sec1.3.txt:187–200 (the induction):
    > "This allows us to define by induction two Cauchy sequences (qi) ∈A{r−1T } and
    > (Ri) ∈As−1[T ] such that ∥f − (gqi +Ri)∥ ≤ κi∥f ∥ … We start with (q0,R 0) = (0, 0).
    > … Then we set qi+1 :=qi +q′ and Ri+1 :=Ri +R′."
  - Lean ↔ source: `g·q_i + R_i ∈ divisionSet g s` with residual `≤ θ^i ‖f‖ → 0` says
    exactly `f ∈ closure (divisionSet g s)` — the closure packaging of the source's
    sequences (see composition note under R1-internal below).
  - Discharge: induction on `i` applying L15 to the residual `f − (gq_i + R_i)`;
    `divisionSet` is an `AddSubgroup` carrier (project `divisionAddSubgroup`,
    NormMulClass-free) so partial sums stay in the set; `θ^i‖f‖ → 0` by
    `tendsto_pow_atTop_nhds_zero_of_lt_one`.
  - Attacks: [2] `θ = 0` impossible (L14 gives `0 < θ`) — no `0^0` corner; `f ∈
    divisionSet` already: closure membership trivial ✓. [3] no completeness needed for
    *closure membership* (only for L17/L18) — matches the source's ordering, which
    invokes completeness only at "by completeness … the sequences have a limit".
    [5] `divisionAddSubgroup` public + `omit [NormMulClass R]` (grepped ✓).
    Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L17** (leaf): `isClosed_divisionSet_of_isMulDistinguished`.
  - Lean: `WeierstrassDivision.lean:110`.
  - Source: martin-sec1.3.txt:198–201:
    > "By construction ∥qi+1 −qi∥ = ∥q′∥ ≤ κi ∥f ∥/∥g∥ and ∥Ri+1 −Ri∥ = ∥R′∥ ≤ κi∥f ∥,
    > so these sequences are well Cauchy sequences. … Now, by completeness of A{r−1T }
    > and As−1[T ] the sequences (qi) and (Ri) have a limit … which satisfy f =gq +R
    > as we wanted."
  - Lean ↔ source + composition note: the source runs "differences are Cauchy ⇒ limits
    exist ⇒ limit satisfies the equation". Our L16+L17 package the same argument: the
    approximants form a sequence IN `divisionSet` converging to `f`; closedness of
    `divisionSet` (proved from the SAME difference-bounds, applied to a convergent
    sequence of decompositions) hands back the limit decomposition. The two proofs use
    identical estimates; only the bookkeeping differs (and it mirrors the project's
    existing `isClosed_divisionSet`, WeierstrassDivision.lean:251, whose proof is
    adapted with L11-bounds in place of the NormMulClass bounds; its `private`
    helper `exists_toRestricted_eq_of_coeff_eq_zero` (:224) is re-derived locally —
    public ingredients `coeff_continuous` (:185), `isClosed_setOf_coeff_eq_zero`
    (:195) reused).
  - Attacks (composition attack, internal-node style): could L16+L17 be true and
    Prop 1.27 fail? No: closure ⊆ closed set = set, membership in `divisionSet` IS the
    division. Could L17 fail while the source's direct-limit argument works? The
    closedness proof uses the same L11 bounds on differences of decompositions the
    source uses on increments — if one works the other does. [2] edge: `divisionSet`
    at `s = 0` = `{gq}` = closed ideal-like set: the bound argument never divides by
    `s` ✓. [5] `CompleteSpace (Restricted A c)` instance exists (Complete.lean:65 ✓);
    limit-remainder-is-polynomial via coeff-vanishing + local re-derivation. Verdict:
    SURVIVED.
  - Prior-B2: log empty.

- **L18** (assembly): `weierstrassDivision_exists_of_isMulDistinguished` = R1.
  - Lean: `WeierstrassDivision.lean:117`.
  - Source: Prop 1.27 statement, martin-sec1.3.txt:141–146 (quoted at L11).
  - Proof plan: `(L17 …).closure_subset (L16 …)` membership unfold — 3 lines.
  - Attacks: composition only; covered under L16/L17. Verdict: SURVIVED.
  - Prior-B2: log empty.

## Result R2: `weierstrassPreparation_exists/…_unique_of_isMulDistinguished` — [Mar16, Cor 1.28]

### Plain-English proof (transcribed from martin-sec1.3.txt:221–252)

Divide `T^s` by `g` (Prop 1.27): `T^s = gq + R`, `deg R < s`, with the norm identity.
Set `w := T^s − R = gq` — monic of degree `s`. By Lemma 1.26(2), `‖gq‖` is attained at
index `s + k₀`; since `w` is a polynomial of degree `s`, necessarily `k₀ = 0`, so every
positive Gauss term of `q` is strictly below `‖q₀‖`. The degree-`s` coefficient of
`gq = w` is `1 = g₀q_s + … + g_s q₀`, and each non-diagonal product is strictly smaller
in norm than `g_s q₀`, so `‖g_s q₀‖ = 1` and `g_s q₀ = 1 − (small)` is a multiplicative
unit (Remark 1.22); as `g_s` is a multiplicative unit, so is `q₀`, and
`q = q₀(1 + Σ_{i>0} (q_i/q₀) T^i)` with the bracket a multiplicative unit of `A{r⁻¹T}`
(Remark 1.22 in the series ring, using `‖q_i/q₀‖r^i < 1` from `k₀ = 0`). Hence `q` is a
multiplicative unit; `e := q⁻¹`, `ω := w` give `g = e·ω`. Uniqueness: `g = e·ω` with
`ω = T^s − R'` monic rearranges to a Weierstrass division `T^s = g·e⁻¹ + R'`, pinned by
division uniqueness (:249–252).

### Leaves

- **L19** (leaf): `norm_coeff_mul_norm_coeff_zero_of_eq_pow`.
  - Lean: `WeierstrassPrep.lean:37`.
  - Source: martin-sec1.3.txt:236–241:
    > "The coefficient of degree s in gq being 1, (because gq =Ts −R), we have the
    > equality 1 = g0qs +g1qs−1 +... +gsq0 and since k0 = 0, and g is T -distinguished
    > of order s, we obtain … that ∥gsq0∥> ∥gs−iqi∥ for i = 1...s . So ∥gsq0∥ = ∥1∥ = 1"
  - Lean ↔ source: with `‖g_s q₀‖ = ‖g_s‖‖q₀‖` (multiplicative unit), the quoted
    display is exactly our conclusion `‖g_s‖·‖q₀‖ = 1`.
  - Discharge: coefficient-`s` computation from `hEq` (`deg R < s`), the ultrametric
    sum equality (same tool as L9), `NormOneClass` for `‖1‖ = 1`, L20 for the
    strictness inputs (or prove L20 first — ticket order fixes L20 → L19; they share
    the `k₀ = 0` setup).
  - Attacks: [2] `s = 0`: sum is the single term `g₀q₀`, no strictness needed ✓;
    trivial ring excluded by `NormOneClass` (attack: `1 = 0` would make `hEq`
    degenerate — cannot occur). [3] `CompleteSpace` NOT needed here (source doesn't
    use it) — kept out of this lemma's hypotheses ✓. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L20** (leaf): `gaussTerm_lt_norm_coeff_zero_of_eq_pow`.
  - Lean: `WeierstrassPrep.lean:45`.
  - Source: martin-sec1.3.txt:230–236:
    > "Since g is T -distinguished of order s, according to lemma 1.26, and if we
    > denote by k0 the greatest index such that ∥qk0∥rk0 = ∥q∥, and w = ∑ s l=0 wlTl, we
    > obtain ∥w∥ = ∥gq∥ = ∥(gq)s+k0 ∥rs+k0 = ∥ws+k0 ∥rs+k0. But since w ∈As[T ],
    > necessarily, s +k0 =s and k0 = 0. Hence, by definition of k0, for all k >0,
    > ∥q0∥> ∥qk∥rk."
  - Lean ↔ source: the final display, quantified over `k > 0`.
  - Discharge: `q ≠ 0` (else `w = T^s − R = 0`, impossible: coefficient `s` is 1 and
    `NormOneClass` gives nontriviality); L6 for `k₀`; L9 for the attained coefficient;
    `w` has zero coefficients above `s` ⇒ `‖w_{s+k₀}‖ ≠ 0` forces `k₀ = 0`.
  - Attacks: [1] does `‖(gq)_{s+k₀}‖ ≠ 0` really follow? = `‖g_s‖‖q_{k₀}‖` (L9), both
    factors nonzero (unit with positive norm — via `‖g_s‖‖q₀‖`-positivity from the
    achieving equations; pressed and closes). [2] `s = 0`: `k₀ = 0` immediate, the
    ∀-conclusion still contentful ✓. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L21** (leaf): `isNormMulUnit_of_eq_pow`.
  - Lean: `WeierstrassPrep.lean:53`.
  - Source: martin-sec1.3.txt:241–248:
    > "and gsq0 = 1 − (gs−1q1 +...g 0qs), with ∥gsq1 +...g 0qs∥< 1. Thus, gsq0 is a
    > multiplicative unit. Moreover, since gs is also a multiplicative unit, q0 is also
    > a multiplicative unit, and ∥q0∥ = ∥gs∥−1. Hence (1.12) q =q0(1 + q1/q0 T +... )
    > and since k0 = 0 … ∥qi/q0∥ri < 1 for all i> 0. Hence 1 + q1/q0 T +... is a
    > multiplicative unit of A{r−1T }, and according to (1.12), q is also a
    > multiplicative unit."
  - Lean ↔ source: conclusion `IsNormMulUnit q` in `Restricted A c`; the chain uses
    L3 twice — once in `A` (for `g_s q₀`), once in `Restricted A c` (for `1 + small`),
    the latter needing the `NormOneClass`/`CompleteSpace`/`IsUltrametricDist` instances
    on `Restricted A c` (all exist: GaussNorm.lean:278/:285, Complete.lean:65 —
    grepped ✓).
  - Discharge: L19+L20 + L3 + L1(mul) + L2(inv, for `q₀ = g_s⁻¹·(g_s q₀)`);
    implementation of (1.12): `u := C q₀⁻¹ * q` hmm — `q = C q₀ * u` with
    `‖u − 1‖ < 1` from L20 and multiplicativity of `q₀⁻¹`; `C`-scalars in `Restricted`
    are mult units when their `A`-value is (small helper inside the ticket:
    `IsNormMulUnit.toRestricted_C`, folded here since the source treats it as obvious).
  - Attacks: [3] hidden-assumption hunt: the `C`-scalar helper is genuinely needed and
    not in the skeleton as a separate decl — accounted inside this leaf's ticket with
    its own 3-line proof (Gauss norm of `C a * f` = `‖a‖‖f‖` when `a` is a mult unit,
    coefficientwise); flagged so it is not silently skipped. [2] `q` with `q₀ = q`
    (constant): bracket = 1 ✓. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L22** (assembly + one addition): `weierstrassPreparation_exists_of_isMulDistinguished`.
  - Lean: `WeierstrassPrep.lean:63`.
  - Source: Cor 1.28 statement + closing of existence proof, martin-sec1.3.txt:221–249:
    > "Corollary 1.28. Weierstrass Preparation. Let g ∈A{r−1T } be a T -distinguished
    > element of order s. There exists an unique couple (w,e ) ∈As[T ]×A{r−1T } such
    > that w is a monic polynomial of degree s, e is a multiplicative unit of A{r−1T },
    > and g =ew." … "So if we set e :=q−1, and w =Ts −R we have the expected result."
  - Lean ↔ source: identical, with one **documented addition**: the clause
    `‖toRestricted c ω‖ = c^s` (not in Martin; matches the project's endpoint shape).
    Its proof is supplied here, not left to drift: `ω = X^s − R` with
    `‖X^s‖ = c^s` (`NormOneClass`) and `‖R‖ ≤ ‖X^s‖ = c^s` (L11 r-bound applied to the
    defining division), so ultrametrically `‖ω‖ ≤ c^s`, while `norm_coeff_mul_pow_le`
    at the monic coefficient `s` gives `≥`. Shared-witness existential (ω, e are one
    witness pair) — statement-splitting exception, justified: the five clauses all
    describe the single factorisation.
  - Attacks: [3] the added norm clause is the only drift from the source — isolated,
    with its own proof; attack on it: `c < 1` vs `c > 1` both fine (no monotonicity
    used). [2] `s = 0`: `ω = 1`, `e = g` — `g` mult-distinguished of order 0 means
    `g` itself has mult-unit constant coefficient dominating; `e = g·1⁻¹` unit ✓.
    Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L23** (leaf): uniqueness — `weierstrassPreparation_omega_unique_…`, `_e_unique_…`.
  - Lean: `WeierstrassPrep.lean:72`, `:82`.
  - Source: martin-sec1.3.txt:249–252:
    > "As for the uniqueness of this decomposition, if g = ew, e and w being as in the
    > statement of the corollary, then w =Ts +R with R ∈As−1[T ], and Ts =w −R =
    > e−1g + (−R) which is the Weierstrass division of Ts byg. Hence e and R are unique
    > and w too because w =Ts +R."
    (Sign conventions in the extraction are garbled; the argument is as transcribed in
    the prose proof above.)
  - Lean ↔ source: split per one-conclusion rule into ω-uniqueness and e-uniqueness;
    hypotheses take only `IsUnit e` (the source's mult-unit is not needed for
    uniqueness — a documented strengthening), and no completeness (matches the
    argument, which only invokes division uniqueness = L12).
  - Discharge: rearrange `g = e·ω` to `toRestricted (X^s) = g * ↑e⁻¹ +
    toRestricted (X^s − ω)` (monic degree `s` ⇒ `deg (X^s − ω) < s`), apply L12.
  - Attacks: [3] hypothesis-weakening attack SUCCEEDED benignly: `IsUnit e` suffices
    (recorded; statement generalised beyond source). [2] `s = 0`: `ω_i = 1` both,
    `e_i = g` ✓. [4] drift: none beyond the recorded weakening. Verdict: SURVIVED.
  - Prior-B2: log empty.

- **L24** (leaf, bridge — structural): `weierstrassDivision_exists_of_normMulClass`,
  `weierstrassPreparation_exists_of_normMulClass`.
  - Lean: `WeierstrassPrep.lean:96`, `:103`.
  - Source: none (bridge; the mathematical content is L5's iff). Discharged by L18/L22
    + `isMulDistinguished_iff_isDistinguished` + `IsNormMulUnit.isUnit`.
  - Attacks: [5] instance availability: `NormMulClass (Restricted …)` NOT needed
    (the iff is applied at coefficient level) ✓. Verdict: SURVIVED.
  - Prior-B2: log empty.

## API gaps
None. Every leaf is discharged from mathlib (cited, grep-verified), from project code
(cited by file:line), or is a small self-contained argument fully transcribed from the
source with a verbatim quote. No leaf is REVIEW-PENDING.

## Confidence gate (Step 5) — all seven conditions
1. Every leaf discharged/mathlib/project as listed ✓
2. Skeleton compiles: `lake build` success, sorry warnings only (2026-07-28) ✓
3. Verbatim quote + match paragraph per leaf ✓ (L4, L24 are marked structural bridges)
4. Adversarial pass per leaf with ≥3 attack categories, all survived; two fixes
   recorded (L13 `Nontrivial`, L15 `0 < θ`), one benign strengthening (L23) ✓
5. Prior-B2 log consulted: empty file, no matches possible ✓
6. Tree mirrors §1.3's own structure (1.20→1.21→1.22→1.24→1.26(2)→1.26(1)→(1.8)→
   uniqueness→Euclid→κ→(1.11)→iteration→1.27→1.28), LOC estimates in tickets grounded
   in the txt line counts ✓
7. Single-conclusion check: all leaves single-conclusion; L22 is a documented
   shared-witness existential; L11/L12/L23 split into per-part declarations ✓
