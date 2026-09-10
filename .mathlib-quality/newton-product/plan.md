# Development Plan — `newton-product` (the Newton polygon of a product)

**BOARD PATH: `.mathlib-quality/newton-product/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  Every `/beastmode` run must name this board
path explicitly (`.mathlib-quality/newton-product/tickets.md`) and keep its own sentinel
`.mathlib-quality/newton-product/beastmode_active` (never the root one, never another board's).
Planned 2026-09-09.

**Files owned by this board**: `PhD/NewtonPolygons/Face.lean`, `PhD/NewtonPolygons/Product.lean`
(both new, skeletoned, building with sorry warnings only; registered in `PhD.lean`).  Do not edit
any other file.  In particular `Height.lean`, `Support.lean`, `SpecConstruction.lean` and
`PhD/ForMathlib/Analysis/Normed/Ring/NegLogNorm.lean` are **read-only** for this board: every
downstream `PhD/LWX/*` file rebuilds when they change, and the `lwx-theta` board is running
concurrently (its sentinel is live).  Lemmas that would naturally live there
(`heightFun_sub_eq_sum`, the two `negLogNorm` sum lemmas, `pointHeight_eq_coe`) are proved in the
board's own files and flagged for relocation at `CLEANUP-FINAL`, a user decision.

**Build**: `lake build PhD.NewtonPolygons.Product` (builds `Face` first; 2084 jobs, ~30 s warm).

**Supersedes**: ticket `T-AG3` of `.mathlib-quality/lwx-theta/` ("The Newton polygon of a product
— API GAP, no statement pre-written").  That board's owner should point T-AG3 at this board once
its run allows an edit; this board does not write to `lwx-theta/`.

## Goal

The Newton polygon of a product of two power series over an ultrametric field is the Minkowski sum
of the two polygons, in the height form the project's `IsNewtonPolygonOf` architecture uses:

```lean
theorem IsEntireNewtonPolygonOf.height_mul [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (n : ℕ) :
    Pfg.height n = Pf.minkowskiHeight Pg n
```

where `minkowskiHeight P Q n = min_{i + j = n} (P.height i + Q.height j)` and
`IsEntireNewtonPolygonOf v P` bundles: `P` is the Newton polygon of `v` (the spec), anchored at
`x = 0`, no `⊥` unit slope, slopes unbounded (finite polygon, or slopes `→ +∞`).  Corollaries:

* **the initial segment** (what [LWX, §3.23 Step I] consumes through `lwx-theta` S3/T-AG3): if
  the first `n` slopes of `g` are at most every slope of `f`, the polygon of `fg` agrees with that
  of `g` up to `n` — `height_mul_of_forall_le`, `unitSlope_mul_of_forall_le`, and for a polynomial
  factor `height_newtonPolygon₀OfPowerSeries_mul_coe` (**milestone**);
* **multiplicities add** ([Ked07, Cor. 2]): the number of slopes `≤ σ` (`faceRight`) and `< σ`
  (`faceLeft`) of `fg` is the sum over the factors — `faceRight_mul`, `faceLeft_mul`;
* closure: the product's polygon again has unbounded slopes (`slopesUnbounded_mul`, `mul`).

## Why "unbounded slopes" is the hypothesis (and cannot be dropped)

`(1 − X) · ∑ Xⁱ = 1`: the polygon of `∑ Xⁱ` is the horizontal ray, that of `1 − X` a unit segment
of slope `0`, their Minkowski sum the horizontal ray — but the polygon of `1` is a single point.
The product formula fails as soon as one factor has a final ray, and [Kob84, §IV.4 Lemma 6] needs
a convergence hypothesis on the closed disc for exactly this reason ("It remains to show that, in
the case when the Newton polygon of `f(X)` has a final infinite slope `λ_f`, `g(X)` also does;
and, if `f(X)` converges on `D(p^{λ_f})`, then so does `g(X)`").  `SlopesUnbounded` — every real is
exceeded by a unit slope, `⊤` counting — is the clean polygon-level hypothesis: polynomials satisfy
it through the junk tail (Kedlaya's "we conventionally put in `+∞` as a slope"), entire series
through `line_le_height` (affine floors of every slope), and it is preserved by products.

## References

- **[Ked07]** K. S. Kedlaya, *p-adic differential equations*, MIT 18.787 (fall 2007), unit "Newton
  polygons", §§1–2, `kskedlaya.org/18.787/newton-poly.pdf`; local text
  `scratchpad …/refs/kedlaya-newton-poly.txt` (this session) — the primary source: Proposition 1
  (Robba) and Corollary 2 with proofs.  The book *p-adic Differential Equations* (CUP 2010) §2.1
  contains the same material.
- **[Kob84]** N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58:
  Ch. IV §3 (p. 97: the definition of the polygon and of its vertices), §4 Lemma 5 (p. 101, radius
  of convergence = sup of slopes) and Lemma 6 (p. 102, the product with a linear factor, proved by
  the exact mechanism used here).  PDF `~/Desktop/Papers/Koblitz - …pdf`.
- **[Gou20]** F. Q. Gouvêa, *p-adic Numbers*, 3rd ed. (Universitext 2020), §7.4 Problem 343
  ("Let `f(X)` and `g(X)` both be pure polynomials of slope `m`. Show that their product is also
  pure of slope `m`") — a special case of `faceRight_mul`/`faceLeft_mul`.
- **[LWX]** Liu–Wan–Xiao, arXiv:1412.2584v4, §3.23 Step I, `.mathlib-quality/tate-riesz/references/lwx.txt:1811–1822` — the consumer.
- Project: `.mathlib-quality/lwx-theta/{plan,decomposition,tickets}.md` (AG3 / T-AG3, the gap this
  board fills); `PhD/NewtonPolygons/{Height,Spec,Support,CoeffVal,OfSlopes}.lean` (the API used).

## Mathlib and project inventory

| Concept | Status | Our action |
|---|---|---|
| Newton polygons | not in mathlib (grep `NewtonPolygon` empty) | project `PhD/NewtonPolygons/` — USE |
| the spec `IsNewtonPolygonOf`, `height_le`, `isGreatest` | project `Spec.lean` | USE |
| supporting lines `line_le_height`, chord `height_le_chord` | project `Support.lean:151`, `Height.lean:740` | USE (the two spec/convexity workhorses) |
| unit-slope dictionary (`unitSlope_mono`, `height_eq_heightFun`, `heightFun_succ`, `unitSlope_ne_top_of_height_ne_top`, `unitSlope_eq_top_of_height_eq_top`, `height_eq_top_mono`, `height_eq_bot_iff`, `toReal_unitSlope_le`, `unitSlope_eq_of_height_eq`) | project `Height.lean`, `Support.lean` | USE |
| coefficient valuations `coeffVal`, admissibility, anchor | project `CoeffVal.lean` | USE |
| ultrametric sum bound / dominant term | mathlib `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsNonarchimedean.apply_sum_eq_of_lt`; project `le_negLogNorm_add`, `negLogNorm_mul` | USE |
| `Finset.inf` on `WithBotTop ℝ` (`inf_le`, `le_inf_iff`, `inf_le_iff`, `exists_mem_eq_inf`) | mathlib, instances verified (`AddCommMonoid`, `OrderTop`, `LinearOrder`, `AddLeftMono`) | USE |
| `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.notMem_of_lt_sInf` | mathlib | USE |
| restrictedness of products and polynomials | project `PowerSeries.isRestricted.mul`, `Polynomial.isRestricted_toPowerSeries`, `isAdmissible_coeffVal_of_isRestricted` | USE |
| faces of a polygon (`faceLeft`/`faceRight`), `SlopesUnbounded`, `IsEntireNewtonPolygonOf` | not in mathlib, not in project | **DEFINE** (Face.lean) |
| the Minkowski height | not in mathlib, not in project | **DEFINE** (Product.lean) |
| the product formula and corollaries | not in mathlib, not in project | **PROVE** |

Gauss norms (`PowerSeries.gaussNorm`, mathlib's `Polynomial.gaussNorm_mul`) are Kedlaya's `v_r`
and could give the exactness step; the plan uses the direct antidiagonal argument instead
because the project's `gaussNorm` API is radius-indexed and shadowed (see memory
`gaussnorm-architecture`), and the direct argument is three lines.

## File structure

- `PhD/NewtonPolygons/Face.lean` (imports `Support`) — `SlopesUnbounded`, `faceLeft`, `faceRight`,
  supporting lines from convexity, `IsEntireNewtonPolygonOf`, and the spec consequences (vertices
  are points; `⊤` beyond the last point; unbounded slopes from affine floors).
- `PhD/NewtonPolygons/Product.lean` (imports `Face`, `CoeffVal`) — `minkowskiHeight` and API, the
  face of the Minkowski sum, the ultrametric coefficient lemmas, the theorem, the corollaries, the
  constructed-polygon and polynomial-factor forms.

## Dependency graph

```
Face.lean
  F01 heightFun_sub_eq_sum ─► F02 line_le_height_of_unitSlope ─► F03 strict lines ─► F04 linearity
  F05 face indices (sInf API) ─► F06 face heights ─► F07 face lines (needs F02, F03)
  F08 spec basics ─► F09 vertex is a point (needs F03) ─► F12 face endpoints are points (F05, F09)
  F10 ⊤ beyond last point   F11 unbounded slopes from affine floors (F01/F02 style)
Product.lean
  P01 minkowskiHeight API ─► P02 subgradient line (F02) ─► P03 exists_subgradient
  P04 face of the sum (F07, P02) ─► P05 linear on the face (F06, P04)
  P06 ultrametric sums ─► P07 coefficient bound / exactness ─► P08 points above the sum (F08)
  P09 ≥ (P01–P03, P08, F10)          P10 exact points at face endpoints (P04, P07, F12)
  P11 ≤ (P03, P05, P10, F05)  ─► [CLEANUP-ALL-1] ─► P12 height_mul (MILESTONE)
  P13 initial segment (P12)   P14 multiplicities add, closure (P12, P04, P05, F05)
  P15 constructed polygons satisfy the hypotheses (F08, F11) ─► P16 constructed corollaries
  P17 polynomial degree finite ─► [CLEANUP-ALL-2] ─► P18 polynomial factor (MILESTONE, LWX-facing)
```

## Generality decisions

1. **Anchors at `x = 0`, not `a₀ = 1`.**  The core theorem needs only nonzero constant
   coefficients (`P.starting_point.1 = 0`); the blueprint normalisation `a₀ = 1` enters only in
   the two initial-segment corollaries where `Pf.height 0 = 0` makes the statement read
   `height (fg) n = height g n`.  General anchors (`a₀ = 0`) are out of scope: the Minkowski
   formula then needs the min restricted to `i ≥ ord f`, and every consumer has `a₀ = 1`.
2. **`IsEntireNewtonPolygonOf` is a structure, not four hypotheses**, because the same four
   appear in a dozen statements; its fields are exactly what the proofs use.  The no-`⊥`
   field is representation hygiene: a spec-satisfying polygon can carry the junk unit slope `⊥`
   (the degenerate one-point representation, cf. `b2_log.jsonl` 2026-08-03), on which
   `unitSlope_eq_of_height_eq` and the face definitions are meaningless; constructed polygons of
   admissible sequences never do (`newtonPolygon₀OfSeq_unitSlope_ne_bot`).
3. **Spec level first, constructed polygons second** (the directory's design rule, `OfSlopes.lean`
   docstring): the theorem is about any three spec-satisfying polygons; the
   `newtonPolygon₀OfPowerSeries` forms are corollaries via existence + uniqueness.
4. **No merge/`⊕` operation on polygons.**  The height form `minkowskiHeight` is the honest
   Minkowski sum at the level the consumers read (heights and unit slopes); building the merged
   polygon as a `NewtonPolygon₀` would need a merge of two monotone `WithBotTop ℝ`-sequences with
   junk tails and is not needed by any consumer.  A follow-up can add it on top of `faceRight_mul`.
5. **`[IsUltrametricDist K]` only where the ultrametric inequality is used** (Product.lean's
   coefficient lemmas and everything downstream); Face.lean is pure polygon geometry.
6. **`hn : Pg.height n ≠ ⊤` was dropped** from the initial-segment corollaries during the
   adversarial pass: when it fails, the slope hypothesis forces every unit slope of `f` to be `⊤`
   (so `f` is a constant) and both sides are `⊤`.

## ChatGPT validation (1h)

Skipped: the `chatgpt-math` MCP server failed to connect this session.

## Hand-off

After user approval: `/beastmode` on `.mathlib-quality/newton-product/tickets.md`.  First
available tickets (no dependencies): F01, F05, F08, F10, P01, P06, P17 — up to **7 workers** in
parallel at the start (two files, disjoint declarations; assign tickets explicitly).
