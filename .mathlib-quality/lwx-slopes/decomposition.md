# Decomposition for lwx-slopes ([LWX] §3.23 Step II, §4.1–4.2, coefficient level)

Planned 2026-09-05.  Source: [LWX] = Liu–Wan–Xiao, arXiv:1412.2584v4 (printed page = PDF
page).  Secondary locators `lwx.txt:N` = line `N` of the `pypdf` extraction (see `plan.md`).
Every quote below is verbatim from that extraction (hyphenation/spacing artifacts of the
extraction are reproduced, subscripts flattened: `bn,λ(n)` = `b_{n,λ(n)}`, `nk` = `n_k`).

## Skeleton location

The Lean skeleton (every lemma stated with `:= by sorry`) lives in:

| File | Lines | `sorry` |
|---|---|---|
| `PhD/NewtonPolygons/Support.lean` | 89 | 5 |
| `PhD/LWX/Sharpness.lean` | 136 | 10 |
| `PhD/LWX/UpperPolygon.lean` | 146 | 17 |
| `PhD/LWX/Vertices.lean` | 278 | 23 |
| `PhD/LWX/Claim.lean` | 140 | 10 |
| `PhD/LWX/SlopeRatios.lean` | 106 | 6 |

`lake build PhD.NewtonPolygons.Support PhD.LWX.Sharpness PhD.LWX.UpperPolygon
PhD.LWX.Vertices PhD.LWX.Claim PhD.LWX.SlopeRatios` passes (2542 jobs, sorries only, no type
errors) — verified 2026-09-05 after the adversarial fixes (two-hulls lemma deleted; `p = 1`
counterexamples fixed by `1 < p`) and after the library-overlap audit of `Support.lean` (two
redundant dictionary lemmas dropped in favour of `Height.lean`'s; the false `unitSlope_ne_bot`
replaced by the constructed-polygon `⊥`-exclusion).

## Notation

`t = Fintype.card ι`; `λ(n) = lwxLambda p t n`; `c_n = charCoeff (D.op ω) n : HaloInt p`;
`b_{n,m} = (charCoeff (D.op ω) n) m : ℤ_[p]` (`m : ℤ`); `c_n(T₀) = PowerSeries.coeff n
(specCharSeries D ω ψ T₀) = ∑' m, ψ(b_{n,m})·T₀^m`; `v(x) = −log‖x‖` (`negLogNorm`), so
`v(T₀) = −Real.log ‖T₀‖ =: vT ∈ (0, log p)` on the annulus and `v(p) = Real.log p`;
`NP_T = newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)`;
`n_k = touchX p t k = k·p·t`; `Λ⁺(n) = lwxUpperTwice p t n / 2` (the upper bound polygon);
`μ = min(vT, log p − vT)` (the [LWX] margin `min{v(T), 1 − v(T)}`).

---

## Result R1: [LWX, Corollary 3.18], the sharpness clauses (`Sharpness.lean`)

### Source proof, read in full
[LWX, p. 23, lwx.txt:1681–1697].  Statement:
> "Corollary 3.18. For T∈ Cp with 0 < v(T ) < 1, we have v(cn(T ))≥ λ(n)v(T ) for every
> n≥ 0, with equality holding if and only if bn,λ(n)∈ Z×p . Moreover, if bn,λ(n) /∈ Z×p , then
> v(cn(T ))≥λ(n)v(T ) + min{v(T ), 1−v(T )}."

Proof (one paragraph):
> "First note that if ∑m∈ZdmTm∈ Λ>1/p, then v(dm)≥ max{0,−m}. Combining this fact with
> (3.16.1), we get v(bn,m)≥ max{λ(n)−m, 0}. For T∈ Cp with 0 <v (T )< 1, we deduce
> (3.18.1) v(bn,mTm)≥ max{λ(n)−m, 0} +mv(T )≥λ(n)v(T ), with the second equality holding
> if and only if m = λ(n). It follows that we always have v(bn,mTm)≥λ(n)v(T ), with equality
> holding if and only if m =λ(n) and bn,λ(n) is a p-adic unit in Zp. The rest of the
> corollary is clear."

### Plain-English proof (source structure preserved)
The coefficient bound `v(b_{n,m}) ≥ max(λ(n)−m, 0)` is Tier 1 (`norm_coeff_charCoeff_upOp_le`).
(3.18.1) is a case split on `m`: for `m < λ(n)`, `v(b_{n,m}T^m) ≥ (λ(n)−m)(1−v(T)) + λ(n)v(T)
≥ λ(n)v(T) + (1−v(T))`; for `m > λ(n)`, `≥ m v(T) ≥ λ(n)v(T) + v(T)`; for `m = λ(n)`,
`= λ(n)v(T)` iff `b_{n,λ(n)}` is a unit and `≥ λ(n)v(T) + 1` otherwise.  "The rest is clear"
is the ultrametric principle: a sum with exactly one term of minimal valuation has that
valuation (equality clause), and a sum all of whose terms have valuation `≥ B` has
valuation `≥ B` (margin clause, `B = λ(n)v(T) + min{v(T), 1−v(T)}`).  The "only if" of the
equality clause is the margin clause plus `min{v(T), 1−v(T)} > 0`.

### Leaves

- **S1** (leaf, new general lemma): `TateFredholm.norm_tsum_lt_of_forall_lt`
  - Lean declaration: `PhD/LWX/Sharpness.lean:38`
    ```lean
    theorem norm_tsum_lt_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {B : ℝ} (hB : 0 < B)
        (hlt : ∀ i, ‖f i‖ < B) : ‖∑' i, f i‖ < B
    ```
  - Source: the ultrametric principle behind "The rest of the corollary is clear"
    [p. 23, lwx.txt:1697]; the general fact is standard ([Gouvêa, *p-adic Numbers*, Cor 4.1.7
    "in an ultrametric space, if a series converges and all terms have |aₙ| < B then |∑| … "],
    here in the form needed for the *strict* inequality).
  - Lean ↔ source match: the source uses "the strict inequality survives summation"; since
    infinitely many terms are involved, strictness needs `f → 0` (all but finitely many terms
    are `< B/2`); this is the hypothesis `hf`, available as `tendsto_spec_cofinite` /
    `summable_specialize` in `HaloRing.lean`.
  - Discharged by: `Filter.eventually_cofinite` (finite exceptional set `S` for `‖f i‖ ≥ B/2`),
    `Finset.exists_max_image` on `S`, `TateFredholm.norm_tsum_le_iSup` + `ciSup_le`
    (verified: all four names `#check`ed 2026-09-05).
  - Attacks attempted:
    - [1] Counterexample search: without `hf`, `f i = B·(1 − 1/i)` on `ℕ` is not summable, the
      `tsum` is `0 < B` — vacuous; with `hf` the sup is attained on a finite set, no
      counterexample.  `lean_local_search` for `norm_tsum_lt`: nothing in the repo.
    - [2] Edge cases: `ι` empty (`tsum = 0 < B` ✓ needs `hB`); `f = 0` ✓; `B` exactly the norm of
      one term — excluded by `hlt` strict.
    - [3] Hypothesis test: `hB : 0 < B` is necessary (`ι` empty, `B = 0` gives `0 < 0`);
      `CompleteSpace E` needed for the `tsum` to be meaningful (else `tsum = 0` and the lemma is
      trivially true — harmless); no hidden assumption.
    - [4] Source drift: the source states no such lemma; this is the explicit form of "the rest
      is clear".  Recorded as infrastructure, not as a [LWX] claim.
    - [5] Discharge: `norm_tsum_le_iSup : Tendsto f cofinite (𝓝 0) → ‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖`
      (Tate.lean:445) — matches; composition of 3 lemmas + a finite max, ≤ 3 ✓.
  - Prior-B2: no name/shape match (6 entries checked across both logs).
  - Verdict: SURVIVED.

- **S2** (leaf, new general lemma): `TateFredholm.norm_tsum_eq_of_forall_lt`
  - Lean declaration: `PhD/LWX/Sharpness.lean:44`
    ```lean
    theorem norm_tsum_eq_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {i₀ : ι} {B : ℝ}
        (hi₀ : ‖f i₀‖ = B) (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < B) : ‖∑' i, f i‖ = B
    ```
  - Source: "with equality holding if and only if m =λ(n) and bn,λ(n) is a p-adic unit"
    [p. 23, lwx.txt:1695–1697] — the "unique minimal term" principle.
  - Lean ↔ source match: the source concludes `v(∑) = min` when the minimum is attained once;
    `B = ‖f i₀‖` is the unique maximal norm.
  - Discharged by: `Summable.tsum_eq_add_tsum_ite` (split off `i₀`), S1 on the rest (with the
    `B = 0` edge handled: then all other terms vanish), `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
    (verified).
  - Attacks attempted:
    - [1] Counterexample: `f i₀ = 1`, all other `f i = 1 − ε_i → 1`? violates `hf`.  With `hf`:
      the rest has norm `< B` by S1, so `‖f i₀ + rest‖ = max = B` ✓.
    - [2] Edge cases: `B = 0` (then `hlt` forces `f = 0` off `i₀` — if `ι = {i₀}` the sum is
      `f i₀`, norm `0` ✓; otherwise `hlt` says `‖f i‖ < 0`, impossible, so `ι = {i₀}`); `ι = {i₀}` ✓.
    - [3] Hypotheses: `hf` needed (S1); `hi₀` could be weakened to `≤`? No — then the rest could
      dominate.  Minimal.
    - [4] Drift: none; the source's "equality iff" is exactly unique-dominant-term.
    - [5] Discharge: `Summable.tsum_eq_add_tsum_ite : Summable f → ∑' n, f n = f b + ∑' n, if n = b then 0 else f n`
      ✓ (`#check`ed); summability from `TateFredholm.summable_of_tendsto_cofinite hf` ✓; 3 lemmas.
  - Prior-B2: none.  Verdict: SURVIVED.

- **S3** (leaf, project): `norm_coeff_mul_zpow_le_of_lt` — [LWX, (3.18.1)], case `m < λ(n)`
  - Lean declaration: `PhD/LWX/Sharpness.lean:61`
    ```lean
    theorem norm_coeff_mul_zpow_le_of_lt (hp2 : p ≠ 2) (D : UpDatum p ι) (ω …) (ψ …) (hψ …)
        {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
        (hm : m < lwxLambda p (Fintype.card ι) n) :
        ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ ≤
          ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * ((p : ℝ)⁻¹ / ‖T₀‖)
    ```
  - Source: "(3.18.1) v(bn,mTm)≥ max{λ(n)−m, 0} +mv(T )≥λ(n)v(T )" [p. 23, lwx.txt:1694]
    and, sharpened for the Claim, "(4.2.1) v(bl,mTm)≥λ(l)−m +mv(T )≥λ(l)v(T )−v(T ) + 1"
    [p. 30, lwx.txt:2264].
  - Lean ↔ source match: for `m < λ`, `λ−m+mv = λv + (λ−m)(1−v) ≥ λv + (1−v)`; in norms
    `‖b T₀^m‖ ≤ p^{m−λ}‖T₀‖^m = ‖T₀‖^λ (p⁻¹/‖T₀‖)^{λ−m} ≤ ‖T₀‖^λ (p⁻¹/‖T₀‖)` since
    `0 < p⁻¹/‖T₀‖ < 1` and `λ − m ≥ 1`.  Exactly (4.2.1)'s first inequality chain.
  - Discharged by: `norm_coeff_charCoeff_upOp_le` (Halo.lean:146, gives `‖b_{n,m}‖ ≤ p^{m−λ}`
    for all `m : ℤ`), `norm_mul`, `norm_zpow`, `hψ`, `zpow_le_zpow_right_of_le_one₀`,
    `mul_zpow`; the `‖T₀‖^λ·(p⁻¹/‖T₀‖)^{λ−m}` rearrangement is `HaloRing.lean:670–697`'s
    `hkey` pattern verbatim.
  - Attacks attempted:
    - [1] Counterexample: `m` negative: `‖b_{n,m}‖ ≤ p^{m−λ} ≤ p^{−λ−1}` and `‖T₀^m‖ = ‖T₀‖^m` large,
      product `≤ p^{m−λ}‖T₀‖^{m}`, and `(p⁻¹/‖T₀‖)^{λ−m} ≤ p⁻¹/‖T₀‖` still holds ✓ (exponent ≥ 1).
    - [2] Edge: `m = λ − 1`: equality of the two bounds ✓; `λ = 0` then no `m < 0`… `m = −1`:
      `‖b_{n,−1}‖ ≤ p^{−1}`, fine ✓.
    - [3] Hypotheses: `h0` needed (`p⁻¹/‖T₀‖ < 1`), `h1` not needed here (kept for uniform
      signatures — flagged as over-specified but harmless; the worker may `omit` it via the
      linter if unused); `hp2` needed only through `norm_coeff_charCoeff_upOp_le`.
    - [4] Drift: (4.2.1)'s `≥ λv − v + 1` is `≤ ‖T₀‖^λ·(p⁻¹/‖T₀‖)` in norms ✓ no drift.
    - [5] Discharge: `norm_coeff_charCoeff_upOp_le` type checked (Halo.lean:146–150) ✓ sorry-free ✓.
  - Prior-B2: none.  Verdict: SURVIVED.

- **S4** (leaf, project): `norm_coeff_mul_zpow_le_of_gt` — (3.18.1), case `m > λ(n)`
  - Lean declaration: `PhD/LWX/Sharpness.lean:70`; statement: `… ≤ ‖T₀‖ ^ λ * ‖T₀‖`.
  - Source: (3.18.1) [lwx.txt:1694], `max{λ−m,0} = 0`, `m v(T) ≥ (λ+1)v(T)`.
  - Lean ↔ source: `‖b‖ ≤ 1` (`HaloInt` bound / `PadicInt.norm_le_one`) and `‖T₀‖^m ≤ ‖T₀‖^{λ+1}`.
  - Discharged by: `PadicInt.norm_le_one`, `zpow_le_zpow_right_of_le_one₀` (verified).
  - Attacks: [2] `m = λ+1` equality ✓; [3] `h0` unused here — over-specified for uniformity
    (same note as S3); [5] discharge 2 lemmas ✓; [4] no drift.  Prior-B2: none.  SURVIVED.

- **S5** (two leaves, project): `norm_coeff_mul_zpow_of_isUnit` (`Sharpness.lean:78`),
  `norm_coeff_mul_zpow_le_of_not_isUnit` (`:87`) — the diagonal term
  - Source: "with equality holding if and only if m =λ(n) and bn,λ(n) is a p-adic unit"
    [lwx.txt:1695–1697]; the non-unit case is `v(b) ≥ 1`.
  - Lean ↔ source: `IsUnit b ↔ ‖b‖ = 1` (`PadicInt.isUnit_iff`); `¬IsUnit b → ‖b‖ ≤ p⁻¹`
    (`PadicInt.norm_le_pow_iff_norm_lt_pow_add_one` at `n = −1` + `‖b‖ < 1`).
  - Discharged by: `PadicInt.isUnit_iff`, `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`,
    `PadicInt.norm_le_one`, `norm_mul`, `norm_zpow`, `zpow_natCast` (verified).
  - Attacks: [2] `λ = 0`, `n = 0`: `b_{0,0} = 1` unit, term `= 1 = ‖T₀‖^0` ✓; [3] no `h0 h1`
    needed — correctly omitted from these two signatures; [5] `PadicInt.isUnit_iff : IsUnit z ↔ ‖z‖ = 1` ✓.
    Prior-B2: none.  SURVIVED.

- **S6** (leaf, assembly of S3/S4): `norm_coeff_mul_zpow_lt` (`Sharpness.lean:97`)
  - Source: "with the second equality holding if and only if m = λ(n)" [lwx.txt:1695].
  - Discharged by: S3 (`m < λ`) with `p⁻¹/‖T₀‖ < 1`, S4 (`m > λ`) with `‖T₀‖ < 1`,
    `mul_lt_of_lt_one_right`, `pow_pos`.  Attacks: [2] `m = λ` excluded by `hm` ✓;
    [3] both `h0 h1` genuinely needed (strictness) ✓; [5] 2 project + 2 mathlib ✓.  SURVIVED.

- **S7** (leaf): `norm_specCharSeries_coeff_eq_of_isUnit` (`Sharpness.lean:107`) — the
  equality clause.
  - Source: Cor 3.18 "with equality holding if and only if bn,λ(n)∈ Z×p" (⇐ direction)
    [lwx.txt:1682].
  - Lean ↔ source: `c_n(T₀) = ∑' m, ψ(b_{n,m})T₀^m` (`specCharSeries`, `PowerSeries.coeff_mk`,
    `HaloInt.specialize`); the diagonal term has norm `‖T₀‖^λ` (S5), all others `<` (S6), so
    S2 gives the norm exactly.
  - Discharged by: S2, S5, S6, `HaloInt.summable_specialize`/`tendsto_spec_cofinite`
    (HaloRing.lean:652; the `Tendsto` form is `private theorem tendsto_spec_cofinite` — the
    worker re-derives `Tendsto` from `Summable` via `Summable.tendsto_cofinite_zero` ✓ mathlib).
  - Attacks: [1] none; [2] `n = 0`: `c₀ = 1`, `λ(0) = 0`, `‖1‖ = 1 = ‖T₀‖^0` ✓ consistent with
    `specCharSeries_coeff_zero`; [3] all hypotheses used; [4] no drift; [5] ≤ 3 project lemmas ✓.
    SURVIVED.

- **S8** (leaf): `norm_specCharSeries_coeff_le_of_not_isUnit` (`Sharpness.lean:117`) — the
  margin.
  - Source: "Moreover, if bn,λ(n) /∈ Z×p , then v(cn(T ))≥λ(n)v(T ) + min{v(T ), 1−v(T )}"
    [lwx.txt:1683–1685].
  - Lean ↔ source: `−log(‖T₀‖^λ·max(‖T₀‖, p⁻¹/‖T₀‖)) = λ vT + min(vT, log p − vT)` ✓; every
    term is `≤ ‖T₀‖^λ·max(…)` by S3 (`m<λ`), S5 (`m = λ`, `p⁻¹ ≤ p⁻¹/‖T₀‖`), S4 (`m > λ`);
    `norm_tsum_le_iSup` + `ciSup_le`.
  - Discharged by: S3, S4, S5, `TateFredholm.norm_tsum_le_iSup`, `le_max_left/right`.
  - Attacks: [2] `‖T₀‖ = p^{−1/2}` (both margins equal) ✓; [3] `h1` needed for
    `p⁻¹ ≤ p⁻¹/‖T₀‖` ✓; [4] the source's additive `min` ↔ multiplicative `max` checked above ✓;
    [5] 5 ingredients but each a one-liner — accepted as the "sup over three cases" leaf.
    SURVIVED.

- **S9** (assembly): `norm_specCharSeries_coeff_eq_iff` (`Sharpness.lean:127`) —
  `⟨fun h hu => by … S8 … max < 1, S7⟩`; the "only if" uses `‖T₀‖^λ·max(…) < ‖T₀‖^λ`.
  Source: Cor 3.18 statement [lwx.txt:1681–1683].  Attacks: [3] needs `p⁻¹/‖T₀‖ < 1` and
  `‖T₀‖ < 1` ✓ both available.  SURVIVED.

---

## Result R2: [LWX, Lemma 4.1] and the band identities (`UpperPolygon.lean`)

### Source proof, read in full
[LWX, p. 29, lwx.txt:2159–2222].  The upper bound polygon:
> "in the course of the proof of Theorem 1.3, we already show that the Newton polygon of
> ∑n≥0cn(T )Xn passes through the points (nk,λ (nk)v(T )) for all k≥ 0. Therefore, we deduce
> that the Newton polygon of ∑n≥0cn(T )Xn always lies below the polygon with vertices
> (nk,λ (nk)v(T )) for allk≥ 0. We call this polygon the upper bound polygon"

> "Lemma 4.1. The maximal vertical diﬀerence between the lower bound polygon and the upper
> bound polygon is (p2− 1)tv(T )/8 for p> 2, and tv(T ) for p = 2.
> Proof. We only treat the casep> 2, the casep = 2 being similar. Note that the lower bound
> polygon and the upper bound polygon touch at the vertices ( nk,λ (nk)v(T )) for k≥ 0. It
> is suﬃcient to bound their vertical diﬀerence over x∈ [nk,nk+1]. By (3.23.1), we ﬁrst get
> λ(nk+1) = ( k + 1)2p(p− 1)t/2. A short computation then shows that the restriction of
> the upper bound polygon on [ nk,nk+1] is a linear function with slope ( k + 1/2)(p− 1)v(T ).
> On the other hand, for every integer a∈ [0,p− 1], by Theorem 3.16, we know that the
> restriction of the lower bound polygon on [ nk +at,nk + (a + 1)t] is a linear function with
> slope (k(p− 1) +a)v(T ). We therefore deduce that the maximal vertical diﬀerence over
> [nk,nk+1] is achieved when a = (p−1)/2. In that case, put n = nk + (p− 1)t/2. It is
> straightforward to see the vertical diﬀerence at x = n is, by looking at the incremental
> diﬀerences of slopes built from the vertex (nk,λ (nk)v(T )), ∑_{i=nk}^{n−1}((k+1/2)(p−1) −
> (⌊i/t⌋ − ⌊i/pt⌋))v(T ) = tv(T ) ∑_{j=kp}^{kp+(p−1)/2−1}((k+1/2)(p−1) − (j − ⌊j/p⌋))
> = tv(T ) ∑_{j=0}^{(p−1)/2−1}((p−1)/2 − j) = 1/8(p2− 1)tv(T ). □"

and the two inputs from §3.23 [p. 25, lwx.txt:1825–1858, 1882–1887]:
> "(3.23.1) … p/(q(p−1)) λ((k+1)qt) = p/(q(p−1)) ∑_{n=0}^{(k+1)qt−1}(⌊n/t⌋ − ⌊n/pt⌋)
> = p/(q(p−1)) (t ∑_{n=0}^{(k+1)q−1} n − pt ∑_{n=0}^{(k+1)q/p−1} n) = (k+1)2qt/2."
> "ﬁrst note that⌊nk/t⌋−⌊ nk/pt⌋ =kq−kq/p−1 =kϕ(q). So if i∈ Z andnk+1−i≥ 0, then
> λ(nk+1−i)≥λ(nk+1)− (k + 1)ϕ(q)i with equality if and only if i∈ [−t,t ]."

### Plain-English proof (source structure preserved)
(a) *(3.23.1)*: `λ(kpt) = ∑_{i<kpt}(⌊i/t⌋ − ⌊i/pt⌋) = t∑_{j<kp} j − pt∑_{j<k} j`
(each floor value is taken `t`, resp. `pt`, times), `= k²p(p−1)t/2`.  (b) *Upper polygon*:
its increment on `[n_k, n_{k+1})` is `(λ(n_{k+1}) − λ(n_k))/pt = (k+½)(p−1)`, i.e.
`lwxUpperTwice` has increment `(2k+1)(p−1)` there, and it meets the vertices.  (c) *Lemma
4.1*: the block difference `2(upper − lower)` at `n_k + x` is `∑_{i<x}((p−1) − 2⌊i/t⌋)`, a
sum whose terms are `≥ 0` for `⌊i/t⌋ ≤ (p−1)/2` and `≤ 0` after; it is `≥ 0` (the negative
tail exactly cancels the positive head, both `= t(p²−1)/4`) and at most the head
`t·∑_{j<(p−1)/2}((p−1)−2j) = t(p²−1)/4`.  (d) *Band identities*: on `[n_k − t, n_k + t)` the
increment `⌊n/t⌋ − ⌊n/pt⌋` is exactly `k(p−1)`; the increments are monotone
(`monotone_sub_div`) and jump by `1` at `n_k + t` and drop by `1` at `n_k − t − 1`, which
gives the "equality iff `i ∈ [−t, t]`" and the quantitative excess `≥ |i| − t` used by Step II.

### Leaves (all pure `ℕ`/`ℤ` combinatorics; discharged by Mathlib's `Finset`/`Nat` API)

- **U1** `sum_range_mul_div` (`UpperPolygon.lean:37`) — "each floor value is taken `t` times":
  source (3.23.1) [lwx.txt:1843–1855] (the passage `∑_{n<(k+1)qt}⌊n/t⌋ = t∑_{n<(k+1)q} n`).
  Discharge: induction on `m` with `Finset.sum_range_add` (`∑_{i<(m+1)t} = ∑_{i<mt} + ∑_{i<t} f((mt+i)/t)`)
  and `Nat.add_mul_div_left`/`Nat.div_eq_of_lt`.  Attacks: [2] `m = 0` ✓, `t = 1` ✓; [3] `ht`
  needed for `Nat.add_mul_div_left` (with `t = 0` both sides are `0` but the proof route needs
  it) ✓; [5] names verified.  SURVIVED.
- **U2** `touchX_add_div` (`:42`), `touchX_add_div_mul` (`:47`) — floor shifts.  Source: the
  same passage (implicit block decomposition).  Discharge: `Nat.add_mul_div_left` (`(i + b*c)/c
  = i/c + b`), `Nat.div_eq_of_lt`.  Attacks: [2] `touchX_add_div` needs no `i < pt` (fixed at
  planning: the identity is exact for all `i`); `_div_mul` needs `i < pt` (`i = pt` gives
  `k+1`) ✓; [3] `hpt : 0 < p*t` ✓.  SURVIVED.
- **U3** `two_mul_lwxLambda_touchX` (`:52`) — (3.23.1).  Discharge: `lwxLambda`, `Finset.sum_tsub_distrib`
  (the summand `i/t − i/(pt)` has `i/(pt) ≤ i/t`), U1 twice (with `f = id`, block sizes `t`
  and `pt` via `Nat.div_div_eq_div_mul`), `Finset.sum_range_id_mul_two` (`(∑_{j<n} j)·2 = n(n−1)`),
  `ring`/`nlinarith`.  Attacks: [2] `k = 0` ✓ (both 0); `p = 1` (λ ≡ 0, RHS 0) ✓; `t = 0` ✓;
  [4] source has `(k+1)`; ours is `k` — identical statement ✓; [5] ✓.  SURVIVED.
- **U4** `lwxUpperTwice_touchX_add` (`:64`) — block linearity: source "the restriction of the
  upper bound polygon on [nk,nk+1] is a linear function with slope (k+1/2)(p−1)v(T)"
  [lwx.txt:2174–2176].  Discharge: `Finset.sum_range_add`, U2 (`_div_mul`), `Finset.sum_const`,
  `smul_eq_mul`.  Attacks: [2] `x = pt` ✓ (`i < pt`), `pt = 0 ⇒ x = 0` ✓.  SURVIVED.
- **U5** `lwxUpperTwice_touchX` (`:70`) — passes through the vertices: source "the lower bound
  polygon and the upper bound polygon touch at the vertices (nk,λ(nk)v(T))" [lwx.txt:2172].
  Discharge: induction on `k` with U4 (`x = pt`) and U3 (`(2k+1)(p−1)pt = 2λ(n_{k+1}) − 2λ(n_k)`).
  Attacks: [2] `k = 0` ✓; [5] ✓.  SURVIVED.
- **U6** `lwxUpperTwice_sub_two_mul_lwxLambda_eq` (`:77`) — the block difference as the signed
  sum: source "by looking at the incremental diﬀerences of slopes built from the vertex
  (nk,λ(nk)v(T)), ∑_{i=nk}^{n−1}((k+1/2)(p−1) − (⌊i/t⌋ − ⌊i/pt⌋))" [lwx.txt:2182–2199].
  Lean ↔ source: doubled, and `⌊(n_k+i)/t⌋ − ⌊(n_k+i)/pt⌋ = kp + ⌊i/t⌋ − k` (U2) turns
  `(2k+1)(p−1) − 2(k(p−1) + ⌊i/t⌋)` into `(p−1) − 2⌊i/t⌋`.  Discharge: U5 (difference `0` at
  `n_k`), `Finset.sum_range_add`, `lwxLambda` unfolded, U2, `push_cast`, `Finset.sum_sub_distrib`.
  Attacks: [2] `x = 0` ✓; [3] `ht` needed (U2) ✓, `hx` needed (U2 `_div_mul`) ✓.  SURVIVED.
- **U7** `sum_block_nonneg` (`:83`), **U8** `four_mul_sum_block_le` (`:90`) — the unimodal
  signed sum: source "the maximal vertical diﬀerence over [nk,nk+1] is achieved when
  a = (p−1)/2 … = tv(T)∑_{j=0}^{(p−1)/2−1}((p−1)/2 − j) = (p2−1)tv(T)/8" [lwx.txt:2179–2222].
  Lean ↔ source: terms `(p−1) − 2⌊i/t⌋` are `≥ 0` iff `⌊i/t⌋ ≤ (p−1)/2`; the partial sum is at
  most the sum of the nonnegative terms `= t·∑_{j<(p−1)/2}((p−1)−2j) + (zero terms)
  = t(p²−1)/4` (U1 with `f j = (p−1)−2j` over `j < (p+1)/2`, `Finset.sum_range_id_mul_two`),
  and at least the full block sum `= 0` (U6 at `x = pt` with U5, or directly the symmetric
  tail computation).  Discharge: `Finset.sum_le_sum_of_subset_of_nonneg`, U1,
  `Finset.sum_range_id_mul_two`, `Finset.sum_nonneg`, `Int` casts (`push_cast`, `omega`).
  Attacks: [1] `p = 2`, `t = 1`, `x = 1`: sum `= 1`, `4·1 ≤ 3`? FALSE — hence `Odd p` in U8
  (the source's `p > 2`); with `p` odd, `x = (p−1)t/2`: `4·t(p²−1)/4 = (p²−1)t` equality ✓
  (sharp).  [2] `x = 0` ✓; `p = 1`: terms `−2⌊i/t⌋ ≤ 0`, sum `≥ 0` only for `x ≤ t`… wait
  `p = 1`: `x ≤ p·t = t`, all terms `0` ✓.  [3] U7 needs no parity ✓ (checked `p` even:
  head `= tp²/4 =` tail).  [5] ✓.  SURVIVED (U8 with `Odd p`).
- **U9** `two_mul_lwxLambda_le_lwxUpperTwice` (`:96`) — lower ≤ upper: assembled from U6 + U7
  after `n = touchX (n/(pt)) + n % (pt)` (`Nat.div_add_mod`).  Source: Lemma 4.1 (the
  "vertical difference" is a difference of upper over lower; implicit nonnegativity)
  [lwx.txt:2169–2170].  Attacks: [1] `p = 0`: `lwxUpperTwice = 0`, `2λ(n) = 2∑ i/t > 0` — FALSE,
  hence `hp : 0 < p` added at planning ✓; `p = 1` ✓ both `0`.  SURVIVED.
- **U10** `lwxUpperTwice_sub_two_mul_lwxLambda_le` (`:102`) — **Lemma 4.1**: U6 + U8 after the
  same decomposition; `Nat` truncated subtraction is safe by U9.  Attacks: [4] source says
  "maximal vertical difference is `(p²−1)tv(T)/8`" (an equality, attained); we state `≤`
  (attainment is not consumed) — recorded weakening, no drift in the used direction.  SURVIVED.
- **U11** `div_sub_div_eq_of_mem_band` (`:110`) — source "⌊nk/t⌋−⌊ nk/pt⌋ =kq−kq/p−1 =kϕ(q)"
  [lwx.txt:1882–1884] plus the band: for `n ∈ [n_k − t, n_k)`: `⌊n/t⌋ = kp − 1`, `⌊n/pt⌋ = k − 1`
  (for `k ≥ 1`; the interval is empty for `k = 0`); for `n ∈ [n_k, n_k + t)`: `kp`, `k`.
  Discharge: `Nat.div_eq_of_lt_le`/`Nat.le_div_iff_mul_le`/`Nat.div_lt_iff_lt_mul`, `omega`.
  Attacks: [2] `k = 0`: band `[0, t)`: `0 − 0 = 0` ✓; `p = 1`: `0 = k·0` ✓; [3] `hp : 0 < p`
  needed for `⌊n/pt⌋` with `pt > 0` ✓.  SURVIVED.
- **U12** `lwxLambda_touchX_add` (`:116`), `lwxLambda_touchX_sub` (`:121`) — the band
  identities: source "λ(nk+1−i)≥λ(nk+1)− (k + 1)ϕ(q)i with equality if and only if
  i∈ [−t,t ]" (the equality half) [lwx.txt:1885–1887].  Discharge: `lwxLambda_succ`
  (increment form) + U11, induction on `i`.  Attacks: [2] `i = 0` ✓, `i = t` ✓ (`n_k + t − 1`
  still in band); `_sub` with `i ≤ touchX k` ✓ (`k = 0` forces `i = 0`).  SURVIVED.
- **U13** `lwxLambda_touchX_add_ge` (`:128`), `lwxLambda_touchX_sub_ge` (`:134`) — the
  quantitative excess beyond the band: source (same passage, the "only if"), quantified by
  its proof mechanism ("the increments `⌊n/t⌋ − ⌊n/pt⌋` are monotone" = `monotone_sub_div`
  composed with `n ↦ n/t`, Halo.lean:49/`monotone_lwxSlopes`'s argument).  Lean ↔ source:
  at `n = n_k + t` the increment is `kp + 1 − k = k(p−1) + 1` and at `n = n_k − t − 1` it is
  `kp − 2 − (k−1) = k(p−1) − 1` (needs `p ≥ 2` so that `n_k − t − 1 ≥ (k−1)pt + (p−2)t ≥ 0`
  lands in block `k−1` with `⌊n/t⌋ = kp − 2` — attack 2 found `p = 1` fails: `λ ≡ 0` but the
  claimed excess `i − t > 0`; hence `hp : 1 < p`), so each step beyond the band contributes
  at least one extra unit.  Discharge: U12 at `i = t`, `lwxLambda_succ`, `monotone_sub_div`
  (via `lwxLambda_eq_sum_comp`), induction on `i − t`.  Attacks: [1] `p = 1` counterexample
  found and fixed ✓; [2] `i = t` equality ✓; [4] this is a sharpening of the source's "iff"
  (quantified), justified by the source's own increment mechanism; the plain "iff" is U14.
  SURVIVED.
- **U14** `lwxLambda_touchX_add_eq_iff` (`:141`) — the source's statement verbatim (right side):
  `⟨by contrapositive from U13 (excess ≥ 1), U12⟩`.  Attacks: [2] `k = 0`, `p ≥ 2`, `i = t+1`:
  `λ(t+1) = 1 ≠ 0` ✓ so the iff holds at `k = 0` — the earlier `0 < k` hypothesis was
  unnecessary and was removed; `p = 1` would break it (`λ ≡ 0`), hence `1 < p` ✓.  SURVIVED.

---

## Result R3: the Claim of [LWX, §4.2] (`Claim.lean`)

### Source proof, read in full
[LWX, pp. 29–31, lwx.txt:2223–2302].  Statement:
> "Claim: If (l,v (cl(T0)) lies strictly below the upper bound polygon for some l∈ N and
> T0∈ Cp with 0 <v (T0)< 8/((p2−1)t+8), then there exists a unique integerm(l)≥λ(l) such that
> for every T∈ Cp with 0 <v (T )< 8/((p2−1)t+8), (l,v (cl(T ))) lies strictly below the upper
> bound polygon and v(cl(T )) =m(l)v(T )."

Proof, part 1 (the point `T₀`) [lwx.txt:2261–2289]:
> "First note that if 0 <v (T )< 8/((p2−1)t+8) and m<λ (l), then by (3.18.1), we get
> (4.2.1) v(bl,mTm)≥λ(l)−m +mv(T )≥λ(l)v(T )−v(T ) + 1>λ (l)v(T ) + (p2− 1)tv(T )/8.
> On the other hand, since (l,v (cl(T0))) lies strictly below the upper bound polygon, by
> Lemma 4.1, we get v(cl(T0))−λ(l)v(T0)< (p2− 1)tv(T0)/8. Hence for m<λ (l), we obtain
> (4.2.2) v(cl(T0))<λ (l)v(T0) + (p2− 1)tv(T0)/8 <v (bl,mTm0 ) by specializing (4.2.1) to
> T = T0. Therefore, there must be some m ≥ λ(l) such that v(bl,mTm0 )≤v(cl(T0)). Let m(l)
> be the minimal one satisfying this property. It follows that v(bl,m(l))≤v(bl,m(l)Tm(l)0 )
> −λ(l)v(T0)≤v(cl(T0))−λ(l)v(T0)< (p2− 1)tv(T0)/8 < 1, yielding bl,m(l)∈ Z×p . Thus for
> m>m (l), we get (4.2.3) v(bl,mTm)>v (bl,m) +m(l)v(T )≥m(l)v(T ) =v(bl,m(l)Tm(l)).
> Moreover, by the minimality of m(l), for m∈ [λ(l),m (l)− 1], we have (4.2.4)
> v(bl,mTm0 )>v (cl(T0))≥v(bl,m(l)Tm(l)0 ), yielding v(bl,m) > v(bl,m(l)). Hence bl,m∈ pZp
> for those m. Finally, putting (4.2.2), (4.2.3), and (4.2.4) together, we conclude
> v(cl(T0)) =v(bl,m(l)Tm(l)0 ) =m(l)v(T0)."

Proof, part 2 (every `T`) [lwx.txt:2290–2302]:
> "Now let 0 < v(T )< 8/((p2−1)t+8). Since the point ( l,m (l)v(T0)) lies strictly below the
> upper bound polygon for T0, by similarity, the point ( l,m (l)v(T )) lies strictly below the
> upper bound polygon for T as well. Note that (4.2.1) together with Lemma 4.1 imply that for
> m < λ(l), the point (l,v (bl,mTm)) lies above the upper bound polygon. Hence v(bl,mTm)>
> m(l)v(T ) for m<λ (l). For m∈ [λ(l),m (l)− 1], since bl,m∈pZp, it follows that
> v(bl,mTm)≥ 1 +λ(l)v(T )> (p2− 1)tv(T )/8 +λ(l)v(T ). Hence (l,v (bl,mTm)) lies above the
> upper bound polygon by Lemma 4.1, yielding that v(bl,mTm) > m(l)v(T ). For m > m(l), we
> have v(bl,mTm) > m(l)v(T ) by (4.2.3). We thus conclude that v(cl(T )) =v(bl,m(l)Tm(l)) =
> m(l)v(T ). This proves the claim."

### Plain-English proof (source structure preserved)
Part 1 produces, at `T₀`, the minimal `m(l) ≥ λ(l)` with `v(b_{l,m(l)}T₀^{m(l)}) ≤ v(c_l(T₀))`
(it exists: terms `m < λ(l)` are too big by (4.2.1)+Lemma 4.1, so if all `m ≥ λ(l)` terms were
strictly bigger than `v(c_l)` the sum would be too — S1); shows `b_{l,m(l)}` is a unit
(`v(b) < (p²−1)tv/8 < 1`), that all other terms are strictly bigger ((4.2.2)/(4.2.3)/(4.2.4)),
hence `v(c_l(T₀)) = m(l)v(T₀)` (S2).  Since no `b_{l,m}` with `m < λ(l)` or `λ(l) ≤ m < m(l)`
is a unit, `m(l)` is the least unit index — `T`-free (`unitIndex`) — and
`m(l)v(T₀) < Λ⁺(l)v(T₀)` gives `2m(l) < lwxUpperTwice l` (`IsBelowUpper`).  Part 2 repeats the
term comparison at any `T` in the annulus, using only `IsBelowUpper` and the κ-condition.

### Leaves

- **C1** `lwxLambda_le_of_isUnit` (`Claim.lean:52`) — units only at `m ≥ λ(l)`: source
  "v(bn,m)≥ max{λ(n)−m, 0}" [lwx.txt:1692]; for `m < λ`, `‖b‖ ≤ p^{m−λ} ≤ p⁻¹ < 1`.  Discharge:
  `norm_coeff_charCoeff_upOp_le`, `PadicInt.isUnit_iff`, `zpow_le_zpow_right_of_le_one₀`.
  Attacks: [2] `m` negative ✓ (same bound); [3] `hp2` via the Tier-1 export only.  SURVIVED.
- **C2** `isUnit_unitIndex` (`:58`), `not_isUnit_of_lt_unitIndex` (`:64`), `unitIndex_le`
  (`:69`), `lwxLambda_le_unitIndex` (`:74`) — `sInf` spec: `Nat.sInf_mem`, `Nat.sInf_le`
  (contrapositive for `not_…`), C1.  Source: "Let m(l) be the minimal one" [lwx.txt:2276] +
  "Hence bl,m∈ pZp for those m" [lwx.txt:2287] (which identifies the `T₀`-minimal dominant
  index with the least unit index).  Attacks: [2] empty set: `sInf ∅ = 0`, `not_isUnit_of_lt`
  vacuous ✓, `isUnit_unitIndex` needs the existence hypothesis ✓; [5] `Nat.sInf_mem :
  s.Nonempty → sInf s ∈ s`, `Nat.sInf_le : m ∈ s → sInf s ≤ m` ✓ verified.  SURVIVED.
- **C3** `kappa_lt` (`:85`) — the radius condition in additive form: source "0 <v (T )<
  8/((p2−1)t+8)" and (4.2.1)'s "λ(l)v(T )−v(T ) + 1>λ (l)v(T ) + (p2− 1)tv(T )/8"
  [lwx.txt:2261–2265].  Lean ↔ source: `p⁻⁸ < ‖T₀‖^{N}` with `N = (p²−1)t + 8` ⟺
  `−8 log p < −N·vT` ⟺ `N·vT < 8 log p` ⟺ `(p²−1)t·vT < 8(log p − vT)` ✓.  Discharge:
  `Real.log_lt_log`, `Real.log_pow`, `Real.log_inv`, `linarith`.  Attacks: [2] `t = 0`:
  `p⁻⁸ < ‖T₀‖⁸` ⟺ `p⁻¹ < ‖T₀‖` ✓ consistent; [3] `h1` needed for `log‖T₀‖ < 0` direction?
  Actually only `‖T₀‖ > 0` is needed; `h1` kept for uniformity.  SURVIVED.
- **C4** `exists_isUnit_and_coeffVal_eq` (`:95`) — **the analytic core** (part 1 of the proof,
  quoted above, ~25 source lines ⇒ ~120 LOC).  Shared-witness existential (documented
  exception: the witness `m(l)` carries both "unit" and "`v(c_l(T₀)) = m·v(T₀)`"; splitting
  into two existentials would lose the identification of the witnesses).
  Lean ↔ source: `hbelow` is "(l, v(c_l(T₀))) lies strictly below the upper bound polygon"
  (`coeffVal < Λ⁺(l)·vT₀`); the conclusion is "(4.2.2)–(4.2.4) ⟹ v(cl(T0)) = m(l)v(T0)" with
  `b_{l,m(l)} ∈ ℤ_p^×`.  Steps: (i) `hbelow` + U10 (Lemma 4.1: `Λ⁺(l) ≤ λ(l) + (p²−1)t/8`)
  + C3 + S3 ⟹ every `m < λ(l)` term is strictly smaller (in norm) than `c_l(T₀)` ((4.2.2));
  (ii) some `m ≥ λ(l)` has `‖term_m‖ ≥ ‖c_l(T₀)‖` (else S1 gives `‖c_l‖ < ‖c_l‖`); take the
  least such `m` (`Nat.find`); (iii) `‖b_{l,m}‖ ≥ ‖c_l(T₀)‖/‖T₀‖^{λ(l)} > p⁻¹` (via
  `hbelow`, U10, C3), so `b_{l,m}` is a unit (`PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`,
  `PadicInt.isUnit_iff`); (iv) all other terms are strictly smaller than `‖term_m‖ = ‖T₀‖^m`:
  `m' < λ` by (i), `λ ≤ m' < m` by minimality ((4.2.4)), `m' > m` by S4-type bound
  `‖term‖ ≤ ‖T₀‖^{m'} < ‖T₀‖^m` ((4.2.3)); (v) S2 ⟹ `‖c_l(T₀)‖ = ‖T₀‖^m`, i.e.
  `coeffVal = m·vT₀` (`coeffVal_of_ne_zero`, `Real.log_pow`).
  Discharge: S1, S2, S3, S4, U10, C3, `Nat.find`/`Nat.find_min'`, `PadicInt` unit lemmas,
  `HaloInt.summable_specialize`.  Attacks: [1] is `m(l) ≥ λ(l)` automatic? yes by (i) — and
  the statement doesn't even need to assert it (C1 gives it back) ✓; [2] `l = 0`: `c₀ = 1`,
  `coeffVal = 0`, `Λ⁺(0) = 0`, `hbelow : 0 < 0` false — vacuous ✓; `coeffVal = ⊤` excluded by
  `hbelow` ✓; [3] `hκ` genuinely needed (without it `m < λ` terms can dominate:
  `v(term_m) ≈ (λ−m)(1−v) + λv` can be `< Λ⁺v` when `1 − v < (p²−1)tv/8`) ✓; `[Nonempty ι]`
  needed for U10 (`0 < t`) ✓; [4] no drift: statement transcribes (4.2.2)–(4.2.4)'s
  conclusion; [5] every cited name verified; the composition is long (this is the one
  substantial ticket) but every step is a named leaf above.  SURVIVED.
- **C5** `isBelowUpper_of_coeffVal_lt` (`:107`) — from C4: `unitIndex ≤ m` (C2), and
  `m·vT₀ = v(c_l(T₀)) < Λ⁺(l)vT₀` ⟹ `2m < lwxUpperTwice l` (divide by `vT₀ > 0`; `Nat`
  cast).  Source: "the point ( l,m (l)v(T0)) lies strictly below the upper bound polygon for
  T0" [lwx.txt:2291–2292].  Attacks: [3] needs `vT₀ > 0` from `h1` ✓.  SURVIVED.
- **C6** `coeffVal_specCharSeries_eq_unitIndex_mul` (`:118`) — part 2 of the proof (quoted;
  ~12 source lines ⇒ ~90 LOC).  Steps: with `m₀ = unitIndex`: `m < λ` terms: S3 + C3 + U10 +
  `2m₀ < lwxUpperTwice` ⟹ `‖term‖ < ‖T‖^{m₀}` ("(l, v(bl,mTm)) lies above the upper bound
  polygon. Hence v(bl,mTm)> m(l)v(T)"); `λ ≤ m < m₀`: non-unit (C2) ⟹ `‖term‖ ≤ p⁻¹‖T‖^m ≤
  p⁻¹‖T‖^λ < ‖T‖^{Λ⁺} < ‖T‖^{m₀}` ("since bl,m∈pZp … v(bl,mTm)≥ 1 +λ(l)v(T )> (p2− 1)tv(T )/8
  +λ(l)v(T )"); `m > m₀`: `‖term‖ ≤ ‖T‖^m < ‖T‖^{m₀}` ((4.2.3)); `m = m₀`: unit ⟹ `= ‖T‖^{m₀}`;
  S2.  Attacks: [1] without `2m₀ < lwxUpperTwice` the conclusion FAILS (large `m₀`; the `m < λ`
  terms dominate) — that is exactly why `IsBelowUpper` carries the inequality ✓; [2] `l = 0`:
  `IsBelowUpper 0` is false (`unitIndex 0 = 0`, `lwxUpperTwice 0 = 0`) ✓ vacuous; [3] `hκ`
  needed ✓; [4] no drift; [5] verified.  SURVIVED.
- **C7** `le_coeffVal_specCharSeries_of_not_isBelowUpper` (`:129`) — contrapositive of C5
  (`by_contra` + `not_lt`).  Source: the Claim's hypothesis read negatively (the points not
  strictly below the upper polygon for one `T` are not for any `T`) [lwx.txt:2244–2256, the
  "Granting the claim" paragraph, which needs exactly this dichotomy].  Attacks: [2]
  `coeffVal = ⊤` ✓ (`le_top`).  SURVIVED.

---

## Result R4: [LWX, Theorem 1.3, proof Step II] at every halo point (`Vertices.lean`)

### Source proof, read in full
[LWX, pp. 25–26, lwx.txt:1880–1980].  Statement being transcribed [Theorem 1.3, p. 3,
lwx.txt:125–142]:
> "Theorem 1.3. … the space Spc>1/p D is a disjoint union Spc>1/p D =X0 ∐ X(0,1) ∐ X1 ∐ X(1,2)
> ∐ X2 ∐ ··· of (possibly empty) rigid analytic spaces which are ﬁnite and ﬂat over W>1/p via
> wt, such that, for each point x∈XI with I denoting the interval n = [n,n ] or (n,n + 1), we
> have v(ap(x))∈ϕ(q)v(Twt(x))·I."

Step I's output (the touching; out of scope) [lwx.txt:1804–1811, 1865–1874]:
> "Step I: The ﬁrst important observation is that the Newton polygon of ∑n≥0cn(Tχk)Xn touches
> the lower bound polygon at the points Pk := (nk+1,λ (nk+1)v(Tχk))."

Step II [lwx.txt:1880–1980]:
> "Step II: We deduce the decomposition of Spc>1/p D from the touching of polygons. To proceed,
> ﬁrst note that⌊nk/t⌋−⌊ nk/pt⌋ =kq−kq/p−1 =kϕ(q). So if i∈ Z andnk+1−i≥ 0, then
> λ(nk+1−i)≥λ(nk+1)− (k + 1)ϕ(q)i with equality if and only if i∈ [−t,t ]. Since |Tχk|
> =p−p/q(p−1)∈ (1/p, 1), by Corollary 3.18, we have (3.23.2) v(cn(Tχk)) =λ(n)v(Tχk) if and only
> if bn,λ(n) is a p-adic unit in Zp. We have previously shown that the Newton polygon of
> ∑n≥0cn(Tχk)Xn exactly goes through the pointPk = (nk+1,λ (nk+1)v(Tχk)). Note that this does
> not force bnk+1,λ(nk+1) to be a p-adic unit, as the point Pk may not be a vertex for the
> Newton polygon. We thus suppose that the line segment of the Newton polygon of ∑n≥0cn(Tχk)Xn
> passing through Pk lies over [n−k+1,n +k+1] in its x-coordinate. It is clear that if n−k+1̸=
> n+k+1, then this line segment has slope (k + 1)ϕ(q). It follows that n−k+1∈ [nk+1−t,nk+1]
> and n+k+1∈ [nk+1,nk+1 +t]. Moreover, the equivalence (3.23.2) implies that n−k+1 (resp.
> n+k+1) is the minimal index in [nk+1−t,nk+1] (resp. maximal index in [ nk+1,nk+1 +t]) such
> that bn−k+1,λ(n−k+1) (resp. bn+k+1,λ(n+k+1)) is a p-adic unit in Zp. For a uniform treatment
> later, we set n−0 = 0 and n+0 the maximal index in [0 ,t ] such that bn+0,0 is a p-adic unit.
> Now, if we specialize to any point T∈W >1/p ω , we must have (for all i∈ Z≥0)
> v(cnk−i(T ))≥v(T )λ(nk−i)≥v(T )·(λ(nk)−kϕ(q)i), where the ﬁrst inequality is a strict
> inequality if nk−t≤ nk−i < n−k (by the minimality of n−k ) and the second inequality is a
> strict inequality if nk−i < nk−t. In summary, for i∈ Z≥0, we have the inequality
> v(cnk−i(T ))≥v(T )·(λ(nk)−kϕ(q)i), which becomes a strict inequality if nk−i < n−k and
> becomes an equality if nk−i = n−k . Similarly, we have the inequality v(cnk+i(T ))≥v(T )·
> (λ(nk) +kϕ(q)i), which becomes a strict inequality if nk +i > n+k and becomes an equality
> if nk +i = n+k . Moreover, by Corollary 3.18, we see that the diﬀerences in all strict
> inequalities are at least min{v(T ), 1−v(T )}. In summary, we conclude that for every T∈ Cp
> with 0 <v (T )< 1, if n−k ̸=n+k , then the points (n−k,λ (n−k )v(T )) and (n+k,λ (n+k )v(T ))
> are two consecutive vertices of the Newton polygon of ∑n≥0cn(T )Xn. Furthermore, the line
> segment connecting these two vertices has slope kϕ(q)v(T ), and passes through the point
> (nk,λ (nk)v(T )). Otherwise, n−k = nk = n+k is a vertex of the Newton polygon of
> ∑n≥0cn(T )Xn."

and the degree bookkeeping [lwx.txt:1981–2008]:
> "forI =k = [k,k ] or (k,k + 1) with k∈ Z≥0, we deﬁne XI,ω to be the open subspace of
> Spc >1/p D,ω such that for each point z∈XI,ω, we have v(ap(z))∈ϕ(q)v(Twt(z))·I. … Regarding
> the degrees, we must have (3.23.3) ∑_{j=0}^{k−1}(degXj,ω + degX(j,j+1),ω) =n−k ∈ [nk−t,nk] and
> (3.23.4) ∑_{j=0}^{k−1}(degXj,ω + degX(j,j+1),ω) + degXk,ω =n+k ∈ [nk,nk +t]."

### Plain-English proof (source structure preserved; `T`-free reformulation)
The source's Step II has two halves.  *(Half A, from touching to unit indices.)*  Touching
at `P_k` for the weight `T_{χ_k}` plus (3.23.2) forces a unit `b_{n,λ(n)}` on each side of
`n_k` within distance `t`, giving `n_k^−`, `n_k^+`.  In our formalization the hypothesis
`HasUnitBand D ω k` *is* the existence of these units, and Half A is the theorem
`hasUnitBand_of_height_eq`: if `NP_{T₀}` passes through `(n_k, λ(n_k)vT₀)` for one halo point
`T₀`, then `HasUnitBand k`.  Its proof is the contrapositive of the source's inequality
display: if no unit on the left, every data point `n ≤ n_k` lies at least `μ` above the band
line (band non-units by the margin clause S8; further left by the strict excess U13), and
the competitor lemma NP1 (break at `N = n_k + 1`) puts the polygon at `n_k` at least
`μ/(n_k+1)` above `λ(n_k)vT₀` — contradiction; symmetrically on the right (break at
`N = n_k − 1`, slope increment `μ/(t+2)`; `k = 0` is `hasUnitBand_zero`).
*(Half B, the polygon at every `T`.)*  The data points satisfy: `v(c_n(T)) ≥ bandLine(n)` for
all `n` (Cor 3.18 + the band identities/excess); equality at `n_k^±` (equality clause S7);
strict with margin `≥ μ` for `n_k − t ≤ n < n_k^−` and `n_k^+ < n ≤ n_k + t` (margin clause
S8, minimality/maximality), and `≥ bandLine + (|n − n_k| − t)vT` beyond the band (U13).
Then: the polygon is `≥ bandLine` everywhere (supporting line, NP2), `≤ bandLine` on
`[n_k^−, n_k^+]` (its values at the two unit indices are on the line and it is convex:
`height_le_chord`), hence `= bandLine` there and passes through `(n_k, λ(n_k)vT)`; and it is
strictly above the line outside (competitor lemma with the margins) — which is precisely
"two consecutive vertices".  The slope reading follows by the height/unit-slope dictionary
(`Support.lean` and `Height.lean`) and `unitSlope_mono`.

### Leaves

- **V1** `isUnitCoeff_zero` (`Vertices.lean:51`), `hasUnitBand_zero` (`:78`) — source "we set
  n−0 = 0 and n+0 the maximal index in [0 ,t ] such that bn+0,0 is a p-adic unit"
  [lwx.txt:1920–1924]; `c₀ = 1` (`charCoeff_zero`), coefficient `1` at `0` (`HaloInt.coeff_one`).
  Attacks: [2] `t = 0`: both witnesses `n = 0` ✓.  SURVIVED.
- **V2** `leftIndex_mem` (`:83`), `not_isUnitCoeff_of_lt_leftIndex` (`:90`) — source "n−k+1 …
  is the minimal index in [nk+1−t,nk+1] … such that bn−,λ(n−) is a p-adic unit"
  [lwx.txt:1911–1919].  Discharge: `Nat.sInf_mem` (set nonempty from `hb.1`), `Nat.sInf_le`.
  Attacks: [2] `k = 0`: set `⊆ {0}` ✓ `leftIndex 0 = 0`; [5] ✓.  SURVIVED.
- **V3** `rightIndex_mem` (`:96`), `not_isUnitCoeff_of_rightIndex_lt` (`:104`) — same passage
  ("maximal index in [nk+1,nk+1 +t]").  Discharge: `Nat.sSup_mem` (nonempty + bounded by
  `n_k + t`), `le_csSup`.  Attacks: [2] bounded set ✓ (`BddAbove` from the `≤ n_k + t` clause);
  [5] `Nat.sSup_mem : s.Nonempty → BddAbove s → sSup s ∈ s` ✓ verified.  SURVIVED.
- **V4** `rightIndex_le_leftIndex_succ` (`:110`) — `n_k^+ ≤ n_k + t ≤ n_{k+1} − t ≤ n_{k+1}^−`
  (needs `2t ≤ pt`, i.e. `2 ≤ p` ✓ prime).  Source: (3.23.3)/(3.23.4) bookkeeping requires
  `n_k^+ ≤ n_{k+1}^−` (degrees nonnegative) [lwx.txt:1993–2008].  Attacks: [2] `p = 2`
  fine (`2t ≤ 2t`), `t = 0` excluded.  SURVIVED.
- **V5** `bandLine_touchX` (`:123`), `bandLine_add_one` (`:127`), `bandLine_eq_of_mem_band`
  (`:132`) — the line "of slope kϕ(q)v(T), and passes through the point (nk,λ(nk)v(T))"
  [lwx.txt:1972–1976]; on the band it equals `λ(n)·vT` by U12 (both sides of `n_k`).
  Discharge: `ring`, U12, `Nat.cast` lemmas.  Attacks: [2] `n = n_k ± t` endpoints ✓ (U12 at
  `i = t`).  SURVIVED.
- **V6** `le_coeffVal_specCharSeries` (`:142`) — Cor 3.18's inequality in `coeffVal` form:
  `norm_specCharSeries_coeff_le` + `coeffVal_of_ne_zero` + `Real.log_pow` (this is `hlog` inside
  `isBelow_newtonPolygon_specCharSeries`, Halo.lean:224–231, made public).  SURVIVED.
- **V7** `coeffVal_specCharSeries_of_isUnitCoeff` (`:150`) — (3.23.2) "if" direction: S7 +
  `coeffVal_of_ne_zero` (nonzero since norm `= ‖T₀‖^λ > 0`).  SURVIVED.
- **V8** `le_coeffVal_specCharSeries_of_not_isUnitCoeff` (`:159`) — the margin S8 in additive
  form: `−log(‖T₀‖^λ·max(‖T₀‖, p⁻¹/‖T₀‖)) = λvT + min(vT, log p + log‖T₀‖)`; handles the
  `coeff = 0` (`⊤`) case by `le_top`.  Discharge: S8, `Real.log_mul`, `Real.log_max`? (use
  `max` case split), `Real.log_pow`, `Real.log_inv`, `Real.log_div`.  Attacks: [3] `p ≠ 2` only
  via S8 ✓.  SURVIVED.
- **V9** `height_specCharSeries_eq_bandLine` (`:171`) — "the line segment connecting these two
  vertices has slope kϕ(q)v(T ), and passes through the point (nk,λ (nk)v(T ))"
  [lwx.txt:1971–1976].  Proof: (≥) NP2 with `a = bandLine 0`, `b = k(p−1)vT`, points
  `≥ bandLine` (V6 + V5 on the band; U13 beyond: `λ(n)vT ≥ bandLine(n) + (|n−n_k|−t)vT ≥
  bandLine(n)`); (≤) `height_le_chord` between `x = n_k^−` and `z = n_k^+` where
  `height ≤ pointHeight = bandLine` (V7, V2/V3 membership, V5); the chord of a line is the
  line.  Discharge: NP2, `height_le_chord` (Height.lean:740), V2, V3, V5, V6, V7, U13,
  `newtonPolygon₀_starting_point_of_coeff_zero_eq_one` (start `= (0,0)`), `isNewtonPolygonOf_powerSeries`
  (+ admissibility as in Halo.lean:232–242).  Attacks: [2] `n_k^− = n_k^+` (single vertex,
  "Otherwise, n−k = nk = n+k is a vertex") ✓ degenerate chord; [3] `[Nonempty ι]` needed for
  U12/U13 ✓; [4] no drift; [5] all verified.  SURVIVED.
- **V10** `bandLine_lt_height_specCharSeries_of_lt_leftIndex` (`:181`) — "(n−k, …) and (n+k, …)
  are two consecutive vertices" + "the diﬀerences in all strict inequalities are at least
  min{v(T ), 1−v(T )}" [lwx.txt:1954–1971].  Proof: NP1 with `N = n_k^−`, `y₀ = bandLine 0 + μ`,
  slopes `b − μ/N ≤ b`; points: `n < N` ⟹ `pointHeight ≥ bandLine + μ` (V8 for band non-units
  via V2 minimality; U13 + `μ ≤ vT` beyond the band); `n ≥ N` ⟹ `≥ bandLine` (as in V9);
  conclusion `height x ≥ bandLine x + μ(N−x)/N > bandLine x` (`μ > 0`: `0 < vT < log p`).
  Attacks: [2] `N = 0` vacuous ✓ (`x < 0` impossible); [3] `μ ≤ vT` needed for the
  beyond-band points — true by `min_le_left` ✓; [5] NP1's hypothesis shape matches
  (`y₀ + s₁·min(n,N) + s₂·max(n−N,0)` equals `bandLine n + μ(1 − n/N)` for `n ≤ N`) ✓.
  SURVIVED.
- **V11** `bandLine_lt_height_specCharSeries_of_rightIndex_lt` (`:191`) — same source; NP1
  with `N = n_k^+`, `y₀ = bandLine 0`, slopes `b ≤ b + μ/(t+2)`; points `n > N`: band non-units
  (V3 maximality, V8) give `≥ bandLine + μ ≥ bandLine + μ(n−N)/(t+2)` since `n − N ≤ t`;
  beyond the band `n = n_k + t + m`, `m ≥ 1`: U13 gives `≥ bandLine + m·vT ≥ bandLine +
  m·μ ≥ bandLine + μ(n−N)/(t+2)` because `n − N ≤ m + t ≤ (t+2)m`.  Attacks: [1] planning
  found the naive slope increment `μ` (instead of `μ/(t+2)`) FAILS (`n = n_k+t+1`, `N = n_k`
  needs `μ(t+1) ≤ vT`) — fixed by the `t+2` divisor ✓; [2] `m = 1` boundary `t+1 ≤ t+2` ✓;
  [3] `[Nonempty ι]` ✓.  SURVIVED.
- **V12** `height_specCharSeries_touchX` (`:202`) — V9 at `x = n_k` (`n_k^− ≤ n_k ≤ n_k^+`
  by V2/V3) + `bandLine_touchX`.  Source: "passes through the point (nk,λ (nk)v(T ))"
  [lwx.txt:1975] and §4 "passes through the points (nk,λ (nk)v(T )) for all k≥ 0"
  [lwx.txt:2162–2164].  SURVIVED.
- **V13** `hasUnitBand_of_height_eq` (`:214`) — Half A (source quoted: "It follows that
  n−k+1∈ [nk+1−t,nk+1] and n+k+1∈ [nk+1,nk+1 +t]").  Proof: `k = 0` by V1; `k ≥ 1`: by
  contradiction on each conjunct with NP1 as described (breaks `N = n_k + 1` with slopes
  `b − μ/N, b`, and `N = n_k − 1` with slopes `b, b + μ/(t+2)`), yielding
  `height(n_k) > λ(n_k)vT₀`.  Attacks: [1] the left competitor at `N = n_k` (not `n_k+1`)
  would give no strictness at `n_k` — planning chose `N = n_k + 1` ✓; [2] `k = 0` handled
  separately (`n_k − 1 < 0`) ✓; [3] the source assumes touching at the *specific* `T_{χ_k}`;
  we allow any halo `T₀` — strictly more general, no drift in the used direction ✓.  SURVIVED.
- **V14** `unitSlope_specCharSeries_eq_of_mem_band` (`:227`) — NP3 (with NP4) on V9 at `j`, `j+1`
  (both in `[n_k^−, n_k^+]`), `bandLine_add_one`.  SURVIVED.
- **V15** `lt_unitSlope_specCharSeries_of_rightIndex_le` (`:236`) — at `j = n_k^+`: `height(j) =
  bandLine(j)` (V9), `height(j+1)` is `⊤` (then `unitSlope = ⊤` by Height.lean's
  `unitSlope_eq_top_of_height_eq_top`) or finite `> bandLine(j+1)` (V11), so NP3 (with NP4)
  gives `unitSlope j > b·vT`; for `j > n_k^+`, `unitSlope_mono`.
  Source: (3.23.3)/(3.23.4) — slopes after `n_k^+` exceed `kφ(q)v(T)` ("v(ap(z)) ∈
  φ(q)v(T)·(k, k+1)" for `X_{(k,k+1)}`).  Attacks: [2] the polygon ending at `n_k^+`
  (`c_n = 0` for `n > n_k^+`): `unitSlope = ⊤ > b` ✓ handled by the `⊤` lemma.  SURVIVED.
- **V16** `unitSlope_specCharSeries_lt_of_lt_leftIndex` (`:245`) — at `j = n_k^− − 1`:
  `height(j+1) = bandLine` (V9), `height(j) > bandLine(j)` (V10) and finite (convexity between
  `0` and `n_k^−`: `height_le_chord`), NP3 gives `unitSlope j < b·vT`; earlier `j` by
  `unitSlope_mono`.  Attacks: [2] `n_k^− = 0` vacuous ✓; `height(j)` could be `⊤`? no: `≤`
  chord between finite heights ✓.  SURVIVED.
- **V17** `unitSlope_specCharSeries_eq_iff` (`:256`) — **Theorem 1.3, `X_k`**: `⟨…, V14⟩`, with
  the "only if" from V15/V16 (`j ≥ n_k^+` ⟹ `>`, `j < n_k^−` ⟹ `<`).  Source: (3.23.3)/(3.23.4)
  and "v(ap(x))∈ϕ(q)v(Twt(x))·I" for `I = [k,k]` [lwx.txt:141–142, 1993–2008].  Lean ↔ source:
  the set of `j` with slope ratio exactly `kφ(q)` is `[n_k^−, n_k^+)`, of size `n_k^+ − n_k^−
  = deg X_k` (3.23.4 minus 3.23.3).  SURVIVED.
- **V18** `unitSlope_specCharSeries_mem_Ioo` (`:266`) — **Theorem 1.3, `X_{(k,k+1)}`**: V15 at
  `k`, V16 at `k+1`, `Set.mem_Ioo`.  Source: same, `I = (k, k+1)`; multiplicity
  `n_{k+1}^− − n_k^+ = deg X_{(k,k+1)}` (3.23.3 at `k+1` minus 3.23.4 at `k`).  SURVIVED.

---

## Result R5: [LWX, Theorem 1.5], first half, at the polygon level (`SlopeRatios.lean`)

### Source proof, read in full
[Theorem 1.5, p. 4, lwx.txt:169–182]:
> "Theorem 1.5. Letω : ∆→ Z×p be a character. Then there exists λ∈ (0, 1) such that there
> exists a sequence of rational numbers α0(ω),α 1(ω),... in increasing order and tending to
> inﬁnity such that Spc>λ D,ω is a disjoint union ∐i≥0Yi,ω of rigid analytic spaces ﬁnite and
> ﬂat overW>λ ω via wt, such that (1.5.1) v(ap(y)) =ϕ(q)v(Twt(y))αi(ω) for every y∈Yi,ω. More
> precisely, if the tame level is neat, then we can take λ =p^{−8/((p2−1)t+8)} for p> 2"

[§4.2, lwx.txt:2223–2260]:
> "We ﬁrst show the existence ofλ, the sequenceα0(ω),α 1(ω),... and the desired decomposition
> for Spc >λ D,ω. … it suﬃces to show that for T∈ Cp with 0 < v(T ) < 8/((p2−1)t+8), the
> ratios to v(T ) of the slopes (counted with multiplicity) of the Newton polygon of
> ∑n≥0cn(T )Xn are independent of the choice of T . Recall that the Newton polygon of
> ∑n≥0cn(T )Xn is the convex hull of points (n,v (cn(T ))) for all n≥ 0. We consider those
> points which lie below the upper bound polygon. [Claim] … Granting the claim, we conclude
> that there exists a (ﬁnite or inﬁnite) set of positive integers {li}i∈I such that if
> 0 < v(T )< 8/((p2−1)t+8), then the Newton polygon of ∑n≥0cn(T )Xn is the convex hull of
> points {(nk,λ (nk)v(T ))}k≥0 ∐{(li,m (li)v(T )}i∈I. It is then clear that the ratios to
> v(T ) of the slopes of this polygon are independent of T . This yields the existence of the
> sequence α0(ω),α 1(ω),... and the desired decomposition for Spc>λ D,ω."

### Plain-English proof (source structure preserved)
The `T`-free point set is `shapeVal`: `m(l)` at `l ∈ {l_i}` (= `IsBelowUpper`), `λ(n_k)` at
`n_k`, nothing elsewhere.  "The Newton polygon of `∑c_n(T)Xⁿ` is the convex hull of
`vT·shapeVal`" is proved by two `isGreatest` applications: (≥) the polygon `Q` of slopes
`vT·σ` (`σ` = the shape polygon's unit slopes) lies below every data point (`IsBelowUpper`
points by C6 and the shape's `height_le`; the others by C7 and `height_shapePolygon_le`;
`⊤` trivially), so `Q ≤ NP_T`; (≤) the polygon `Q'` of slopes `τ/vT` (`τ` = `NP_T`'s unit
slopes, finite because `NP_T` passes through every touching vertex, V12) lies below every
point of `shapeVal` (by C6 at `IsBelowUpper` points and V12 at the vertices), so
`Q' ≤ shapePolygon`.  Heights agree up to the factor `vT`, hence so do unit slopes: the
slope ratios are `slopeRatio j`, independent of `T`.  (The source's "It is then clear" is
this scaling argument.)

### Leaves

- **P1** `isNewtonPolygonOf_shapePolygon` (`SlopeRatios.lean:54`), `shapePolygon_starting_point`
  (`:59`) — existence of the hull of the `T`-free points: `isNewtonPolygonOf_newtonPolygon₀OfSeq`
  with `∃ i, shapeVal i ≠ ⊤` (`i = 0`: `IsBelowUpper 0` is false since `unitIndex 0 = 0`
  (`c₀ = 1`, C2) and `lwxUpperTwice 0 = 0`; `pt ∣ 0`; value `λ(0) = 0`) and
  `isAdmissible_of_affine_bound` (`m = 0, b = 0`, all values `≥ 0`); start `= (0, 0)` from
  `start_mem`/`start_le`.  Source: "the convex hull of points {(nk,λ (nk)v(T ))}k≥0
  ∐{(li,m (li)v(T )}i∈I" [lwx.txt:2246–2256].  Attacks: [2] `t = 0` would make `pt ∣ n` for
  all… `p·0 = 0 ∣ n` iff `n = 0` ✓ harmless; [5] verified names.  SURVIVED.
- **P2** `height_shapePolygon_le` (`:65`), `height_shapePolygon_ne_top` (`:72`) — the shape hull
  lies below the upper polygon: for `n ∈ [n_k, n_{k+1}]`, `height ≤ chord` (`height_le_chord`)
  between `(n_k, λ(n_k))` and `(n_{k+1}, λ(n_{k+1}))` (`height_le` at the vertices), and the
  chord is `Λ⁺` on the block (U4, U5); finiteness follows.  Source: "always lies below the
  polygon with vertices (nk,λ (nk)v(T ))" [lwx.txt:2164–2166] (for the shape's own hull).
  Attacks: [2] `n = n_k` ✓ (chord endpoint); [3] `[Nonempty ι]` for `pt > 0` ✓.  SURVIVED.
- **P3** `height_specCharSeries_eq_smul_shape` (`:82`) — the two `isGreatest` applications
  (prose above).  Discharge: `height_eq_heightFun` + `heightFun` unfolded for both polygons,
  NP5 (monotone real slopes), NP4, `ofSlopes`, `height_ofSlopes`, `ofSlopes_starting_point`,
  `IsNewtonPolygonOf.isGreatest` (for `NP_T` via `isNewtonPolygonOf_powerSeries`; for the shape
  via P1), `isBelow_iff_height`, C6, C7, P2, V12, `height_eq_top_mono` (finiteness of `NP_T`
  heights from V12: every `n ≤ n_k` for some `k`), `Finset.mul_sum`.  Attacks: [1] is
  `NP_T ≤ vT·shape` at the vertices without a data point there? yes — V12 is a *height*
  statement, not a data-point statement ✓ (this is why `shapeVal` includes the vertices);
  [2] `n` with `c_n(T) = 0` (`⊤`): handled in the (≥) direction by `le_top` ✓; [3] `hband`
  for **all** `k` needed (finiteness + the vertex heights) ✓; `hκ` for C6/C7 ✓; [4] no drift:
  this is "the Newton polygon is the convex hull of …" made precise; [5] all names verified;
  the composition is the second substantial ticket (~150 LOC; source ≈ 8 lines "Granting the
  claim … It is then clear").  SURVIVED.
- **P4** `unitSlope_specCharSeries_eq_slopeRatio` (`:95`) — **MILESTONE** (1.5.1): NP3 on both
  polygons (`≠ ⊥` by NP4; heights finite: P2 and P3), P3 at `j` and `j+1`, `mul_sub`.  Source: "(1.5.1)
  v(ap(y)) =ϕ(q)v(Twt(y))αi(ω)" and "the ratios to v(T ) of the slopes (counted with
  multiplicity) … are independent of the choice of T" [lwx.txt:177, 2228–2234].
  Lean ↔ source: `slopeRatio j = φ(q)·α̃_j(ω)` (slopes with multiplicity), `T`-free by
  construction; `unitSlope_j(T) = vT·slopeRatio j` is (1.5.1) for the `j`-th slope.
  Attacks: [3] "increasing and tending to infinity" not asserted (deferred, plan.md);
  [4] the source's `α_i` are indexed by components `Y_i`; ours by slope position — the
  standard multiplicity reading, as in the source's own `α̃_j` [lwx.txt:185].  SURVIVED.

---

## API gap AG-NP: supporting lines and the two missing dictionary facts (`Support.lean`)

**Library audit (2026-09-05).**  `Height.lean` already provides the height/unit-slope dictionary:
`heightFun` is *defined* as `y₀ + ∑_{i<k} toReal (unitSlope i)` with `height_eq_heightFun`
(so the planned `height_eq_sum_unitSlope` was redundant and is dropped), `heightFun_succ`,
`unitSlope_ne_top_of_height_ne_top`, and — `private` — `unitSlope_eq_top_of_height_eq_top`
(Height.lean:542, `height x = ⊤ → unitSlope ((x − start).toNat − 1) = ⊤`) and
`toReal_unitSlope_le` (Height.lean:658, monotonicity of the real unit slopes below the junk
region).  `OfSlopes.lean:170` provides (`private`) `slopes_zero_ne_bot`: the constructed polygon
of an admissible sequence has `slopes 0 ≠ ⊥`.  The planned `unitSlope_ne_bot (height (j+1) ≠ ⊤)`
was **false**: the degenerate one-point polygon (`support = 1`, `lengths 0 = 0`, `slopes 0 = ⊥`)
has `unitSlope 0 = ⊥` but `height 1 = y₀` finite, because `rightHeight`'s junk guard only tests
`⊤` (Height.lean:542–555 read against Basic.lean:199).  What is genuinely absent from the
library, and what `Support.lean` now contains:

- **NP1** `IsNewtonPolygonOf.twoSlope_le_height` (`Support.lean:71`) — the competitor lemma.
  Discharge: `ofSlopes (fun i => if i < N then s₁ else s₂) (monotone by hs) y₀`;
  `height_ofSlopes` gives `y₀ + ∑_{i<k} (if i < N then s₁ else s₂) = y₀ + s₁·min(k,N) +
  s₂·max(k−N,0)` (`Finset.sum_ite`, `Finset.filter_lt`, `card_range`); `h.isGreatest`
  (`ofSlopes_starting_point` + `hx`) and `isBelow_iff_height`.  The pattern exists only inline
  (Halo.lean:243, QMF/Weight/Slopes.lean:184).  Attacks: [2] `N = 0` (single slope `s₂`) ✓;
  `k ≤ N` and `k ≥ N` ✓; [3] `hs` needed for `Monotone` ✓; `hx` needed to match anchors ✓;
  [5] `isGreatest : ∀ Q, Q.starting_point.1 = P.starting_point.1 → (∀ k, Q.height k ≤ pointHeight v k)
  → Q.IsBelow P` ✓ (Spec.lean:75).  Prior-B2: `NewtonPolygon₀.unitSlope_cases` (T002, resolved)
  concerns junk slopes — irrelevant here (all slopes real).  SURVIVED.
- **NP2** `line_le_height` (`:82`) — NP1 with `s₁ = s₂ = b`, `N = 0`, `y₀ = a`.  SURVIVED.
- **NP3** `unitSlope_eq_of_height_eq` (`:42`) — the unit slope as a height increment, with the
  hypothesis `unitSlope j ≠ ⊥`: `height_eq_heightFun` at `j`, `j+1`; `heightFun_succ`; `toReal`
  of a real slope (`unitSlope_ne_top_of_height_ne_top`, `hb`); `WithBotTop.coe_inj`.  Attacks:
  [1] the degenerate `⊥` polygon with `a = c = y₀` refutes the statement without `hb`
  (found at planning) — `hb` added; [2] `j = 0` ✓; [5] names verified.  SURVIVED (with `hb`).
- **NP4** `newtonPolygon₀OfSeq_unitSlope_ne_bot` (`:60`) — `⊥`-exclusion for constructed
  polygons: `slopes_zero_eq_bot_of_unitSlope_eq_bot` (public) + `slopes_zero_ne_bot`
  (OfSlopes.lean:170, public since 2026-09-05).  Supplies `hb` for
  `NP_T = newtonPolygon₀OfSeq (coeffVal f)` and for `shapePolygon`.  Attacks: [2] `v` with a
  single finite point: the polygon is one `tail`/`⊤` — no `⊥` ✓; [3] admissibility is exactly what
  excludes `Step.unboundedBelow` (`unboundedBelow : nextStep = .unboundedBelow → ¬BddBelow
  (slopeSet …)`) ✓; [5] verified.  SURVIVED.
- **NP5** `monotone_toReal_unitSlope` (`:50`) — the `Monotone` packaging `ofSlopes` needs, from
  `toReal_unitSlope_le` (Height.lean:658, public since 2026-09-05) and
  `unitSlope_ne_top_of_height_ne_top`.  SURVIVED.

Used from `Height.lean` without re-statement: `height_eq_heightFun` + `heightFun` (P3),
`unitSlope_eq_top_of_height_eq_top` (V15; public since 2026-09-05).

---

## Prior-B2 log consultation (Step 4.6)

Logs read: `.mathlib-quality/b2_log.jsonl` (3 entries: `NewtonPolygon₀.unitSlope_cases` /
`lengths_final` (T002, resolved), `LWX.exists_binomial_basis` (C3 of lwx-halo, fixed by
`CharZero` + `ρ ≤ 1`)) and `.mathlib-quality/lwx-halo/b2_log.jsonl` (3 entries: the H4/H5
`T`-rescaled transport statements `cfunSlash_mahlerEmbed`, `mahlerEmbed_seqSlash`,
`seqSlash_coeff` — all three resolved on that board, which is complete).  Name matches: none.
Shape matches: NP4 ↔ T002 (junk slopes) — addressed above.  The lwx-halo H4/H5 entries concern
`IntegralModel.lean`, which this board does not import; no leaf here has that shape.

## Confidence gate (Step 5)

1. Every leaf discharged from Mathlib / project code, or is part of the API gap AG-NP whose
   own leaves are discharged ✓.
2. Skeleton compiles, sorries only ✓ (2542 jobs).
3. Every leaf has a verbatim quote + match paragraph ✓ (infrastructure leaves S1/S2/NP*
   cite the source passage that consumes them and the library spec they instantiate).
4. Every leaf has an attack block with ≥ 3 categories; the pass found and fixed: the
   two-hulls artifact (deleted), `p = 1` counterexamples (U13/U14 hypotheses), `p = 0`
   (U9), the naive right-competitor slope (V11/V13, `μ/(t+2)`), the false `unitSlope_ne_bot`
   (degenerate `⊥` polygon; replaced by NP4 and the `hb` hypothesis of NP3), two redundant
   dictionary lemmas (dropped for `Height.lean`'s), and the unnecessary `i < pt` / `0 < k`
   hypotheses ✓.
5. Prior-B2 consulted; one shape match addressed ✓.
6. Tree mirrors the source: R1 = Cor 3.18's paragraph; R2 = Lemma 4.1's proof + (3.23.1) +
   the band sentence; R3 = the Claim's two-part proof; R4 = Step II's two halves; R5 = "Granting
   the claim".  LOC estimates in `tickets.md` cite source line counts ✓.
7. Single-conclusion: the only bundled leaf is the shared-witness existential C4 (justified);
   V17/V18 are `iff`/`∈ Ioo` single statements; the `∧`-valued *definitions* `HasUnitBand`,
   `IsBelowUpper` are hypotheses, not theorems; V2/V3/`leftIndex_mem` bundle the three
   defining clauses of a `sInf`/`sSup` membership (a `mem` spec, one fact) ✓.
