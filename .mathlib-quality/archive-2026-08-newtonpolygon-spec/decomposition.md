# Decomposition — `IsNewtonPolygonOf`: the Newton polygon as a lower convex hull

Project started 2026-08-03. Predecessor board (Martin Weierstrass, completed 2026-07-28)
archived in `archive-2026-07-martin-weierstrass/`.

## Skeleton location

Every lemma below exists as a `:= by sorry` declaration. `lake build
PhD.NewtonPolygons.SpecConstruction` passes (37 sorry warnings, no type errors) — verified
2026-08-03.

- `PhD/NewtonPolygons/Height.lean` (12 sorries) — discrete convexity for `NewtonPolygon₀.height`
- `PhD/NewtonPolygons/Spec.lean` (8 sorries) — `pointHeight`, `IsNewtonPolygonOf`, uniqueness,
  spec-level extraction, `IsPure`
- `PhD/NewtonPolygons/SpecConstruction.lean` (17 sorries) — admissibility, algorithm line
  bounds, walk correspondence, existence

Existing infrastructure consumed (read in full during planning, unchanged):
`PhD/ForMathlib/NumberTheory/NewtonPolygon/Basic.lean` (518 lines: `NewtonPolygon₀`, `height`,
`IsBelow`), `Construction.lean` (770 lines: `nextStep`, `slopeSet`, `newtonPolygon`,
`nextVertex_*` API), `PowerSeries.lean` (`newtonPolygon₀OfSeq`).

## Sources

- **[BP]** `blueprint/src/chapter/NP.tex` — the project blueprint. Primary source for the
  *statements*.
- **[Kob]** Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions* (2nd ed., GTM 58),
  Ch. IV §3–4. Standard reference defining the Newton polygon of a polynomial/power series as
  the lower convex hull, including the rotating-line construction and the three power-series
  cases (polygon ends, infinite ray, limiting ray). Cross-reference for statement shape only.
- Mathlib: searched 2026-08-03 — **no** Newton polygon, no lower-convex-hull-of-point-set
  machinery. `Mathlib/Analysis/Convex/Slope.lean` (`ConvexOn.slope_mono_adjacent`) is the
  nearest relative but works on `ConvexOn ℝ s f` for real functions, not on the walked
  `WithBotTop`-valued `height`; bridging would cost more than the direct discrete proofs.

**Source-gap disclosure (binding honesty note).** [BP] *defines* the polygon as the hull and
*asserts* the algorithm computes it in one line:

> "It should be clear that by construction this constructs the lower convex hull of the set of
> points $\{(i,\nu (a_i) )\}$ and taking the slopes and lengths of the obtained segments we get
> our corresponding definition in Lean." — [BP], after the algorithm description.

[Kob] IV.3 likewise treats hull-ness of the construction as visually evident. So the existence
and uniqueness *proofs* below are our own expansion of a claim both sources state without
proof (source-gap fallback step 1: the expansion is written out in full as prose here and
becomes the source substrate for the leaves). No leaf below depends on any unproved external
claim beyond elementary convexity arithmetic.

---

## Result R1: the specification and its uniqueness

### Source claim (verbatim, [BP] Definition 1)

> "The *Newton polygon* of $f = \sum a_i x^i$ is the lower boundary of the convex hull of the
> set of points $(i,\nu (a_i))$, where we ignore points with infinite $p$-adic valuation. Here
> by convex hull we mean the smallest convex polygon that contains all points."

### Formalisation decision (Lean ↔ source match)

"Lower boundary of the convex hull" is formalised as: **the greatest convex polygon anchored at
the first point and lying on/below all points.** Convexity is already a structure field of
`NewtonPolygon₀` (`slopes_increasing`), so the spec needs only: anchor (`start_le` +
`start_mem`), minorant (`height_le`), maximality (`isGreatest`). This is the standard
"greatest convex minorant" rendering of "lower boundary of the hull"; [Kob] IV.3 draws the same
picture.

### Plain-English proof of uniqueness

Let P₁, P₂ both satisfy the spec for v. Their starting x-coordinates agree: each start is a
point (start_mem) and has no point strictly left of it (start_le), so each is the least finite
index of v. Hence each is a competitor for the other's `isGreatest`, giving `P₁.IsBelow P₂` and
`P₂.IsBelow P₁`, i.e. pointwise `height` equality by antisymmetry in `WithBotTop ℝ`.

### Leaves

- **L1** (leaf): `pointHeight` + API (`pointHeight_eq_top_iff`, `pointHeight_coe`)
  - Lean: `PhD/NewtonPolygons/Spec.lean:36–43`
  - Discharge: definitional unfolding (`match` on `WithTop`); mathlib `WithTop` case API.
  - Attacks attempted:
    - [edge] `v k = ⊤` → `⊤` ✓; junk-free: no `⊥` output, so `pointHeight` never collides with
      the left-junk region of `height`. No flaw.
    - [hypothesis] Needs no injectivity of `algebraMap Γ ℝ` — heights live in ℝ by design. ✓
    - [discharge] `WithTop` recursor; ≤ 3-step proofs. ✓
  - Verdict: SURVIVED.

- **L2** (leaf, definition): `IsNewtonPolygonOf` (4 fields)
  - Lean: `Spec.lean:60–74`. Compiles.
  - Source: [BP] Definition 1 (quoted above).
  - Attacks attempted (these three shaped the definition; each is a *successful* attack on a
    rejected variant, recorded so it is not re-tried later):
    - [counterexample vs. unanchored maximality] If `isGreatest` quantified over competitors
      with arbitrary starting point, take v with first point at k = 3; a competitor starting at
      k = 0 with huge starting height satisfies "below the points" vacuously at 0..2 (points
      are ⊤) and is not below any candidate; **no P would satisfy the spec**. Fix: competitors
      share the starting x-coordinate. Variant with `start ≤ Q.start` also fails: Q anchored at
      a non-vertex interior point k can have `Q.height k = v k > P.height k`. REJECTED variants;
      current form survives both counterexamples.
    - [counterexample vs. structure-level uniqueness] Points (0,0),(1,1),(2,2) over Γ = ℝ:
      P₁ = one segment (slope 1, length 2), P₂ = two collinear segments (slopes 1,1, lengths
      1,1). Both are valid `NewtonPolygon₀`s (`slopes_increasing` is non-strict), both satisfy
      all four fields. **Structure uniqueness is FALSE**; only height uniqueness (L4) is true.
      A strictness field was considered and rejected: the constructed polygon itself has
      adjacent equal slopes in the vertex-then-`limitingRay` case ([BP]'s own example
      `1 + x + p⁻¹∑xⁿ`, quoted in `Construction.lean:219–221`), so a strict spec would break
      existence (R2).
    - [edge, ⊥-slope representation] For a horizontal hull (all points at one height), the
      degenerate polygon with `slopes 0 = ⊥` has walked height horizontal (`toReal ⊥ = 0` junk)
      and *also* satisfies the spec. Consequence: extraction lemmas must be stated through
      `height`/`toReal (unitSlope 0)` — where the junk value 0 coincides with the true slope in
      the only spec-satisfiable degenerate case — never as `slopes 0 ≠ ⊥`. L17's statement was
      checked against exactly this case.
  - Verdict: SURVIVED (as stated; three neighbouring variants refuted).

- **L3** (leaf): `starting_point_fst_eq`
  - Lean: `Spec.lean:81`. Proof: both starts equal the least finite index; from `start_mem` +
    `start_le` by `le_antisymm` and index chasing. Discharge: elementary.
  - Attacks: [edge] v with a single point: both starts = that index ✓. [hypothesis] does NOT
    need `starting_point.2` equality (algebraMap may be non-injective; y-coordinates could in
    principle differ as Γ-elements — but `start_mem` pins them equal in `WithTop Γ` via
    `WithTop.coe_inj`, stronger than needed). No flaw.
  - Verdict: SURVIVED.

- **L4** (leaves): `isBelow`, `height_eq` (uniqueness headline)
  - Lean: `Spec.lean:85–96`.
  - Discharge: L3 + `isGreatest` applied both ways + `le_antisymm` in `WithBotTop ℝ`
    (`LinearOrder` ✓). ≤ 3 steps each.
  - Attacks: [composition] could L3 + mutual isGreatest hold but heights differ? No —
    `IsBelow` is pointwise ≤, antisymmetry closes. [edge] junk regions: left ⊥ = ⊥ ✓, right
    ⊤ = ⊤ forced by mutual ≤ ✓. Verdict: SURVIVED.

## Result R2: existence — the algorithm constructs the hull

### Source claim (verbatim)

[BP] (quoted in full in the disclosure above): "It should be clear that by construction this
constructs the lower convex hull…". The rotating-line algorithm it refers to:

> "Rotate the line until one of the following happens: The line simultaneously hits infinitely
> many of the points … don't break the line and the polygon is complete. The line reaches a
> position where it can be rotated no further without leaving behind some points … the half
> lines forms the final segment of the polygon. The line hits a finite number of points … break
> at the last point that was hit and repeat the procedure." — [BP], algorithm items 3a–3c.

These three cases are literally `Step.infiniteRay` / `Step.limitingRay` / `Step.nextVertex` of
`Construction.lean` ("rotated no further" = infimum of the slope set; "last point hit" =
`Finset.max'` of the achieving set). The Lean ↔ source match is exact by design of
`Construction.lean`.

### Plain-English proof (our expansion; substrate for leaves L5–L16)

**Hypotheses.** (h1) some point exists; (h2) *admissibility*: every slope set out of a point is
bounded below. Both are necessary: without h1 no anchored polygon exists (L16); without h2 no
polygon lies below the points at all — v k = −k² gives chords from any anchor tending to −∞,
while every `NewtonPolygon₀` height is bounded below by the line of its first real slope
(or is horizontal in the ⊥-junk case) — this is the attack that surfaced h2, recorded at L16.

**Below (height_le).** Induct along the algorithm's steps. At the vertex (i₀, i₁) of step n,
each output determines a line bound on all later points: for `nextVertex j₀ j₁ l m`, m is the
minimum of the slope set, so every point (k, aₖ) with k > i₀ satisfies m(k − i₀) ≤ aₖ − i₁
(and strictly beyond j₀, since j₀ is the *last* achiever); for `limitingRay m` / `infiniteRay
m`, m = inf of the slope set gives the same non-strict bound (strict for limitingRay, whose
infimum is unattained). [This is `step_slope_le` of `Test/test.lean:184–203`, proved there for
`coeffVal K f`; re-proved at `Construction.lean` generality — same `csInf_le` argument.] The
polygon's height on segment n is the line of slope m through (i₀, i₁) (walk correspondence
L11–L12), so the height at any x in segment n is ≤ the point at x by the line bound of the
step whose segment contains x; points left of the anchor don't exist (L10).

**Greatest (isGreatest).** Let Q be anchored at the same x₀, below all points. Show
Q.height x ≤ P.height x segment by segment. Left of x₀ both are ⊥. On segment n with endpoints
Xₙ, Xₙ₊₁ (both *vertices of P touching points*, L12): Q(Xₙ) ≤ v(Xₙ) = P(Xₙ) and
Q(Xₙ₊₁) ≤ v(Xₙ₊₁) = P(Xₙ₊₁); Q is convex, hence below its chord (L8), which is below the chord
of P's endpoint values, which *is* P on the segment (P affine there, L6 + L11). For a final
`infiniteRay`: points ON the ray occur beyond every bound (achieving set infinite, L9b), so
every x right of the last vertex lies between the vertex and an on-ray point, and the chord
argument applies. For a final `limitingRay`: for every ε > 0, points with slope < m + ε from
the last vertex occur beyond every bound (L9a: only finitely many indices lie below any fixed
N, each with slope a fixed real > m, so slopes approaching the unattained infimum come from
arbitrarily far right); the chord argument gives Q(x) ≤ Yₙ + (m + ε)(x − Xₙ) for all ε > 0,
hence ≤ the ray (`le_of_forall_pos_le_add`). For a final `tail` (no points right of the last
vertex): P is ⊤ there, nothing to prove.

**Assembly (L15).** anchor = L10, below = L13, greatest = L14; four fields, one constructor.

### Leaves (Height layer — generic convexity, no algorithm)

- **L5** (leaves): `vertexX` + API (`vertexX_zero/succ/mono`), `heightFun` + API
  (`heightFun_zero/succ`)
  - Lean: `Height.lean:44–66`. Discharge: `Finset.sum_range_succ`, `WithTop` add-monoid
    (⊤-absorbing sums are exactly the intended "vertex at infinity" semantics), `le_add_right`
    monotonicity. All verified present in mathlib (grep + prior use in `Basic.lean`).
  - Attacks: [edge] length-⊤ segment: vertexX (n+1) = ⊤ and stays ⊤ ✓ intended. [edge]
    `vertexX_mono` non-strict only — junk lengths are 0. Statement deliberately `Monotone`. ✓
    [discharge] sums in `WithTop ℤ` need `AddCommMonoid (WithTop ℤ)` — present. ✓
  - Verdict: SURVIVED.

- **L6** (leaves): `unitSlope_eq_slopes`, `unitSlope_cases` — walk ↔ segment correspondence
  - Lean: `Height.lean:73–89`. **Hardest Height leaf.** Proof: induction on the
    `rightSlopeAux` walk mirroring its own documented invariant (`Basic.lean:100–127`: token
    in segment n with r units of it still ahead). The invariant relating (n, r, j) to
    `vertexX n ≤ x₀ + j < vertexX (n+1)` is what the aux recursion preserves; the worked
    example at `Basic.lean:119–125` is the substrate. Sizing: `rightSlopeAux` + docstring is
    ~50 source lines; expect ~120–180 LOC with a private invariant helper.
  - Attacks: [edge] width-0 junk segments (past a terminated polygon): `lengths_nonFinal`
    guarantees interior lengths ≠ 0, so inside the honest region the slide-through branch of
    the aux never fires; `unitSlope_cases`' ⊤ arm covers the junk region. ✓ [edge] first
    segment of length ⊤: `rightSlope` short-circuits to `slopes 0`; vertexX 1 = ⊤ so the
    in-segment condition holds for all j ✓ consistent. [source-drift] checked against the aux
    docstring's worked example (offsets 0,1 → s₀; 2 → s₁): with x₀-relative indexing our
    statement gives the same values. ✓
  - Verdict: SURVIVED.

- **L7** (leaves): `unitSlope_mono`; domain lemmas `height_eq_bot_iff`, `height_eq_top_mono`,
  `height_eq_heightFun`, `unitSlope_ne_top_of_height_ne_top`
  - Lean: `Height.lean:92–113`.
  - Discharge: mono = L6 (cases + eq_slopes) + `slopes_increasing` + ⊤-junk absorbing
    rightwards. `height_eq_heightFun` is the `else` branch of `rightHeight` (definitional
    modulo the guard); `height_eq_bot_iff`: right of start `rightHeight` is never ⊥ (⊤ or a
    real coe); left of start the embedded polygon's `leftSlope` is constantly ⊥ (all
    negative-index slopes are ⊥ under `toNewtonPolygon`), by induction on `leftSlopeAux`
    sliding through width-0 junk.
  - Attacks: [edge] all-⊥ polygon (support 1, slope ⊥): mono holds (constant); heightFun
    horizontal — consistent with L2's third attack. ✓ [edge] `height_eq_top_mono` from a ⊥
    height: hypothesis is `= ⊤`, vacuous ✓. [counterexample search] none found:
    `rightHeight`'s ⊤-guard fires exactly when the incoming unit slope is ⊤, and ⊤ unit
    slopes are upward-closed (L6 cases + junk). ✓
  - Verdict: SURVIVED.

- **L8** (leaves): `heightFun_chord`, `le_heightFun`, `height_le_chord`
  - Lean: `Height.lean:118–139`.
  - Discharge: discrete Jensen from monotone increments. `heightFun` has increments
    `toReal (unitSlope i)`; under the `height ≠ ⊤` guard all increments below c are real (L7)
    or the whole polygon is the constant-⊥ one (increments constantly 0) — in both cases the
    real increment sequence is monotone, and the chord inequality for sums of monotone
    increments is elementary `Finset.sum` induction (division-free form chosen to avoid `div`
    side conditions). `height_le_chord` = `heightFun_chord` + `height_eq_heightFun` +
    ⊥-absorption for y < start.
  - Attacks: [counterexample vs. naive statement] WITHOUT the `height ≠ ⊤` hypothesis the
    chord is FALSE: slopes (1, ⊤) give toReal increments (1, 0), non-monotone. The hypothesis
    is load-bearing; recorded. [edge] a = b = c: both sides equal ✓; z = x in
    `height_le_chord`: division junk `/0 = 0` gives bound `a`, and y = x forces height y ≤ a ✓
    holds. [hypothesis] the division-free ℝ form avoids needing `x < z`. ✓
  - Verdict: SURVIVED.

### Leaves (algorithm layer)

- **L9** (leaves): line bounds `nextStep_slope_le` / `nextStep_slope_lt` /
  `limitingRay_slope_lt` / `infiniteRay_slope_le`; ray approximations
  `limitingRay_exists_slope_lt` (L9a), `infiniteRay_exists_achieving_gt` (L9b)
  - Lean: `SpecConstruction.lean:64–100`.
  - Source: [BP] algorithm items 3a–3c (quoted above); the `nextVertex` non-strict bound is
    the already-proved `Test/test.lean:184` `step_slope_le` (same `csInf_le` argument,
    re-proved at `Construction.lean` generality because test.lean's version is specialised to
    `coeffVal K f`). Discharges: `nextVertex_slope_eq_sInf''`, `nextVertex_bddBelow`,
    `nextVertex_j₀_eq_max` (strict version: k > j₀ = max' of achievers ⟹ k not achieving ⟹
    slope ≠ m; with ≥ m gives >), `limitingRay_slope_eq_sInf` + unattainedness,
    `infiniteRay_slope_eq_sInf`, `Set.Infinite.exists_gt` (verified in mathlib). L9a: the set
    of indices ≤ N with finite value is finite; each has slope > m (unattained); their minimum
    is m + δ for some δ > 0; a slope in (m, m + min δ ε) exists since m is the infimum —
    hence its index is > N. Sizing: test.lean proves the non-strict bound in 20 lines; expect
    ~30 LOC each, ~80 for L9a.
  - Attacks: [edge] no points beyond N at all in L9a? Then the slope set would be *finite*
    (only finitely many candidate indices), its inf attained — contradicting `limitingRay`.
    The conclusion's `∃ k > N` is genuinely forced ✓. [hypothesis] strict `nextVertex` bound
    needs k > j₀ (not k > i₀) — statement checked, correct in skeleton. [source-drift]
    "rotated no further without leaving behind some points" = inf; "last point that was hit"
    = `max'` — matches `nextStep`'s definition verbatim. ✓
  - Verdict: SURVIVED.

- **L10** (leaves): anchors `newtonPolygon₀OfSeq_start_mem` / `_start_le`
  - Lean: `SpecConstruction.lean:108–115`.
  - Discharge: unfold `newtonPolygon₀OfSeq`'s `starting_point` match on `findFirstFinite v 0`;
    `Nat.find_spec` / `Nat.find_min`. Same `Nat.find`-wrangling as the proved
    `findFirstFinite_zero` (`Test/test.lean:156–173`) — this is the ONE place the plan fights
    `Nat.find`, by design.
  - Attacks: [edge] h1 gives the `some` branch; the junk anchor (0,0) of the `none` branch is
    never reached under h1 ✓. [edge] the `.choose` in `findFirstFinite` returns the Γ-value
    with `v (Nat.find h) = coe choose` — exactly `start_mem`'s shape ✓. [discharge]
    `Nat.find_min` gives `start_le` after casting ℤ < to ℕ < (start ≥ 0 from the match) ✓.
  - Verdict: SURVIVED.

- **L11** (leaf): `newtonPolygon₀OfSeq_vertexX` — step n's output vertex is vertex n + 1
  - Lean: `SpecConstruction.lean:120–122`.
  - Discharge: induction on n. Base: vertexX 1 = start + lengths 0 = anchor + (j₀ − anchor)
    (`nextVertex_l_eq : l = j₀ - i₀`, `nextVertex_lt : i₀ < j₀` keep ℕ-subtraction honest).
    Step: chain `newtonPolygon_nextVertex_of_lt` + `nextStep_nextVertex''` to identify step
    n + 1's input vertex with step n's output. Sizing: the corresponding chain lemmas in
    `Construction.lean:574–628` are ~55 lines; expect ~60–90 LOC.
  - Attacks: [edge] n = 0 goes through `findFirstFinite` (i₀ = anchor index) — needs L10's
    unfolding; dependency recorded. [composition] `l = j₀ − i₀` in ℕ with `i₀ < j₀` ✓.
  - Verdict: SURVIVED.

- **L12** (leaf): `newtonPolygon₀OfSeq_height_vertex` — the polygon touches the points at its
  vertices
  - Lean: `SpecConstruction.lean:126–130`.
  - Discharge: L11 (vertex x-coordinates) + L6 (`unitSlope_eq_slopes` inside each segment) +
    `heightFun` telescoping: height(vertex n+1) = height(vertex n) + m·l, and the point value
    j₁ satisfies the same recurrence (`nextVertex_slope_eq_sInf'`: m = slopeReal i₀ j₀ i₁ j₁,
    i.e. algebraMap j₁ = algebraMap i₁ + m(j₀ − i₀) in ℝ). Induction along steps.
  - Attacks: [edge] `height ≠ ⊤` at vertices: interior unit slopes are real
    (`slopes_nonFinal` via L6) so the ⊤-guard never fires at or left of a vertex ✓.
    [composition] could L11 and L6 both hold and the height still miss j₁? No — heightFun is
    *defined* as the slope sum; the telescoping is arithmetic. ✓
  - Verdict: SURVIVED.

- **L13** (leaf): `newtonPolygon₀OfSeq_height_le` — below the points
  - Lean: `SpecConstruction.lean:136–138`. Prose: "Below" paragraph above. Discharge: L9
    (line bound at the step whose segment contains k) + L11/L12 (height on that segment is
    the step's line) + L6. For k in the ⊤-region (past a `tail`): no points remain
    (`slopeSet = ∅` at the last vertex ⟹ all later v k = ⊤ ⟹ pointHeight = ⊤) — uses the
    `tail` slope-set inversion, available as `slopeSet_eq_empty_of_nextStep_tail`
    (`Test/test.lean:227`, to be ported inside this ticket, ≤ 15 LOC).
  - Attacks: [edge] k strictly left of anchor: height = ⊥ ✓ trivial. [edge] k inside an
    *earlier* segment than the current step: the induction must carry "below on
    [anchor, current vertex]" forward, not just the last segment — recorded so the worker
    structures the induction correctly. [edge] `unboundedBelow` step: excluded by h2 via the
    `unboundedBelow` inversion (`Construction.lean:474`) ✓.
  - Verdict: SURVIVED.

- **L14** (leaf): `newtonPolygon₀OfSeq_isGreatest` — maximality
  - Lean: `SpecConstruction.lean:142–148`. Prose: "Greatest" paragraph above. **Hardest leaf
    of the project.** Discharge: L8 (`height_le_chord` applied to Q), L12 (touching), L9a/L9b
    (ray approximations), `le_of_forall_pos_le_add` (verified in mathlib) for the ε-limit in
    the limitingRay case.
  - Attacks: [composition — the ε-argument] does `limitingRay` really provide near-inf slopes
    *beyond every x*? Yes — L9a, whose own attack log covers the "finitely many below N"
    step. [edge] Q above P at a non-integer x? `IsBelow` compares integer heights only, and
    both polygons are affine on unit intervals (`Basic.lean:225–229` docstring records the
    equivalence) ✓ the integer statement is the right one. [edge] segment of length ⊤ inside
    the honest region (`infiniteRay`): the vertex list stops; the on-ray points from L9b
    substitute for the missing right endpoint ✓ handled by the ray case. [edge] Q with
    support ⊤ but P finite (`tail`): past P's end P.height = ⊤ ✓ trivial.
  - Verdict: SURVIVED.

- **L15** (assembly node): `isNewtonPolygonOf_newtonPolygon₀OfSeq` = ⟨L10a, L10b, L13, L14⟩;
  `isNewtonPolygonOf_powerSeries` = L15 at `v = coeffSeq val f` (definitional unfolding of
  `newtonPolygon₀OfPowerSeries`). One line each by design. Lean:
  `SpecConstruction.lean:153–163`.
  - Attacks: [composition] the four fields' hypotheses (h1, h2) match the theorem's exactly;
    no hidden strengthening ✓.
  - Verdict: SURVIVED (assembly).

- **L16** (leaves, converses/degenerate): `not_isNewtonPolygonOf_of_forall_eq_top`
  (`start_mem` yields `⊤ = coe`, absurd; 3 lines); `IsNewtonPolygonOf.bddBelow`
  (admissibility is necessary at the anchor: chords out of the anchor are ≥
  `toReal (unitSlope 0)` by L17; BddBelow witness); `isAdmissible_of_affine_bound`
  (elementary: for points (i₀,i₁), (k,a) on/above the line y = mx + b,
  slopeReal i₀ k i₁ a = (a − i₁)/(k − i₀) ≥ m − (i₁ − m·i₀ − b)/(k − i₀) ≥
  m − max 0 (i₁ − m·i₀ − b), using k − i₀ ≥ 1; explicit BddBelow witness). Lean:
  `SpecConstruction.lean:44–57, 166–168`.
  - Attacks: [arithmetic check on the witness] both signs of the gap i₁ − m·i₀ − b checked;
    with the `max 0` witness the bound holds regardless ✓. [hypothesis] `IsAdmissible`
    quantifies over ALL points, not just the anchor: existence recurses through later
    vertices whose slope sets must also be bounded; quantifying over all points makes
    L13/L14 direct and is implied by the affine bound anyway. Design choice recorded. ✓
    [edge] `not_…_of_forall_eq_top`: no admissibility needed — start_mem alone dies ✓.
  - Verdict: SURVIVED.

## Result R3: spec-level extraction (the test.lean workhorses)

### Source claims (verbatim)

> "A line through the origin with slope $m_1 < m$ passes below all points on the polygon,
> touching it only at $(0,0)$. This means that $v_p(a_j) > m_1 j$ for every $j > 0$."
> — [BP], proof of the first no-zeros lemma (§Properties).

> "We know all points are on or above the line $y = m x$, and the ones where $j > N$ are
> strictly above it." — [BP], proof of Proposition (NP), k = 1 case.

- **L17** (leaf): `unitSlope_zero_mul_le` — points on/above the first-slope line, from the
  spec alone
  - Lean: `Spec.lean:105–110`.
  - Lean ↔ source match: [BP]'s "all points are on or above the line y = mx" with the origin
    replaced by the general anchor (x₀, y₀) and m = first unit slope; [BP]'s normalisation
    a₀ = 1 (anchor (0,0)) is the special case. The strict versions beyond the break are R2's
    L9: they need the algorithm's "last achiever" datum, which the bare spec cannot see —
    deliberate split.
  - Discharge: `height_le` at k + `height_eq_heightFun` + `le_heightFun` (L8) + L7 (height at
    k is not ⊤ since it is ≤ a real pointHeight).
  - Attacks: [edge — the ⊥-representation] horizontal hull represented with `slopes 0 = ⊥`:
    `toReal ⊥ = 0` and the claim becomes v(x₀) ≤ v(k) — TRUE for a horizontal hull's points;
    the junk value coincides with the honest slope in the only spec-satisfiable ⊥ case (L2
    attack 3). The statement survives where a `slopes`-based statement would not. ✓
    [hypothesis] at k = anchor the claim degenerates to 0 ≤ 0; the strict hypothesis keeps
    cast arithmetic clean, harmless. ✓ [counterexample search] none: this is monotone slopes
    + telescoping, checked against a two-segment example by hand. ✓
  - Verdict: SURVIVED.

- **L18** (leaves): `IsPure` + `IsPure.support_eq_one` + `isPure_of_support_eq_one`
  - Lean: `Spec.lean:117–133`.
  - Source (verbatim, [BP]): "A polynomial $f(x)$ is pure if its Newton polygon has only one
    slope."
  - Discharge: `slopes_junk`, `slopes_nonFinal`, `slopes_final` case chase (support ≤ 2 from
    nonFinal at n = 1, then = 1 from final; converse from junk at 1). Elementary `WithTop ℕ`
    order.
  - Attacks: [edge] support = 0: `slopes_junk` forces slopes 0 = ⊤ ≠ coe m ✓ excluded.
    [edge] support = ⊤: slopes 1 real by nonFinal ✓ excluded. [representation] a pure polygon
    *split into collinear pieces* would not satisfy `IsPure` — acceptable: `IsPure` is
    consumed on the constructed polygon (for polynomials: no limitingRay, strict slopes), and
    a height-level purity notion can be added later if ever needed. Recorded limitation.
  - Verdict: SURVIVED (with recorded, deliberate representation-dependence).

## Prior-B2 log consultation

`b2_log.jsonl` read 2026-08-03: **empty (0 entries)**. No name or shape matches possible.
(The three refuted design variants at L2 are recorded there in this document instead, since
they were killed at planning time, before any ticket existed.)

## Confidence gate

1. Every leaf discharged from mathlib (cited: `Finset.sum_range_succ`,
   `Set.Infinite.exists_gt`, `le_of_forall_pos_le_add`, `Nat.find_spec`/`Nat.find_min`,
   `WithTop`/`WithBotTop` order API — all verified present), from project code (cited:
   `nextVertex_*` and `newtonPolygon_*` inversion API in `Construction.lean`, the `Nat.find`
   pattern and `step_slope_le` argument from `Test/test.lean`), or is one of the two flagged
   hard leaves (L6, L14) whose proofs are fully written out in the prose expansion above with
   no external gap. **No API gaps requiring separate sub-development.** ✓
2. Skeleton compiles, sorries only (verified above). ✓
3. Verbatim quotes: [BP] quotes attached to R1, R2, R3 and to each leaf that formalises a
   source claim; leaves L5–L8, L11–L14 are internal to the (disclosed) expansion of [BP]'s
   one-line claim and cite the prose sections above as substrate. ✓
4. Adversarial pass: every leaf and both composite results carry attack logs; three attacks
   *succeeded* against rejected design variants (unanchored maximality, structure-level
   uniqueness, strictness field) and are recorded at L2 to prevent re-introduction. ✓
5. Prior-B2: log empty. ✓
6. Tree mirrors the source where the source has structure ([BP] Definition 1 → L2; algorithm
   items 3a–3c → L9; purity definition → L18) and mirrors the disclosed prose expansion
   elsewhere; LOC estimates grounded (L6 vs. `rightSlopeAux` source length; L9 vs. the proved
   `step_slope_le`; L11 vs. the `Construction.lean` chain lemmas). ✓
7. Single-conclusion: every skeleton declaration has one conclusion; L15 is the marked
   assembly node (anonymous-constructor proof plan). ✓

---

## Execution post-mortem (2026-08-03, appended at board completion)

Two leaf statements were corrected during execution — both survive as *hypothesis
strengthenings*, no conclusion changed, both machine-refuted in their original form:

1. **L6 `unitSlope_cases`** — the skeleton's hypothesis-free form is FALSE: the degenerate
   polygon (`support = 1`, `lengths 0 = 0`, `slopes 0` an arbitrary real) satisfies every
   `NewtonPolygon₀` field, has every `vertexX n = x₀` (no bracket), yet `unitSlope 0 =
   slopes 0 ≠ ⊤`. The planning attack log (L2, attack 3) had found the ⊥-slope face of this
   degenerate representation but not the real-slope face. Fix: hypothesis
   `(P.support = 1 → P.lengths 0 ≠ 0)`; logged in `b2_log.jsonl`; the alternative
   (strengthen `lengths_final` in ForMathlib `Basic.lean` to also force `slopes n = ⊤`)
   is recorded there as a USER DECISION for a future ForMathlib pass.
2. **L8 `height_le_chord`** — needs `(hxs : P.starting_point.1 ≤ x)`: with the left chord
   endpoint in the ⊥-region its `hx` hypothesis is vacuous and a very negative `a` drags the
   chord below the polygon (counterexample: horizontal polygon at (0,0), x = −1, a = −100,
   z = 2, c = 0). The T005 ticket's off-script note pre-authorized exactly this
   strengthening. No consumer affected (all chord applications have x ≥ start).

Everything else landed as decomposed. All 17 proof tickets closed; the milestone
`isNewtonPolygonOf_newtonPolygon₀OfSeq` and all endpoint theorems depend on
`[propext, Classical.choice, Quot.sound]` only.

### Addendum (2026-08-03T21:00Z): lengths_final strengthened, hdeg proviso removed

Per user decision, `lengths_final` on both `NewtonPolygon` and `NewtonPolygon₀`
(ForMathlib `Basic.lean`) now concludes `… ∧ (slopes n = ⊤ ∨ slopes n = ⊥)` — the disjunctive
form the user chose, which outlaws the real-slope phantom while keeping the `unboundedBelow`
⊥-packaging legal (so `newtonPolygon₀OfSeq` needed no junk-convention change, only the new
`newtonPolygon_slopes_of_lengths_eq_zero` companion in `Construction.lean`). Consequences:
`unitSlope_cases` is now HYPOTHESIS-FREE with a `⊤ ∨ ⊥` junk arm (the L6/L2 execution
correction is fully resolved); new public bridge
`slopes_zero_eq_bot_of_unitSlope_eq_bot`; all five files build, zero sorries/warnings,
endpoints on standard axioms. b2_log.jsonl entry 2 records the resolution.
