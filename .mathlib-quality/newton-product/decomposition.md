# Decomposition — `newton-product` (the Newton polygon of a product)

Board `.mathlib-quality/newton-product/`.  Written 2026-09-09 by `/develop` (Phase 1e, run in the
adversarial disposition of `--decompose`).  Every leaf below points at a `:= by sorry`
declaration in the compiling skeleton, carries a verbatim source quote, a Lean ↔ source match
paragraph, an attack log, and a prior-B2 check.

## Skeleton location

- `PhD/NewtonPolygons/Face.lean` — 293 lines, 3 definitions + 1 structure, 29 sorries.
- `PhD/NewtonPolygons/Product.lean` — 451 lines, 1 definition, 42 sorries.

`lake build PhD.NewtonPolygons.Product` passes (2084 jobs; sorry warnings only, no errors) —
verified 2026-09-09 14:30 after the last statement change (dropping `hn`, see P13).  Both files
are imported from `PhD.lean`.

## Sources (with locators)

- **[Ked07]** Kedlaya, *p-adic differential equations* (18.787, fall 2007), unit "Newton polygons".
  Text extracted to `scratchpad …/refs/kedlaya-newton-poly.txt` (`ked.txt:` below): §1 at
  `ked.txt:1–31`, §2 at `ked.txt:32–94`.
- **[Kob84]** Koblitz, 2nd ed.  Text `scratchpad …/refs/koblitz.txt` (`kob.txt:`): §IV.3 p. 97
  at `kob.txt:4089–4118`, Lemma 4 proof p. 98 at `kob.txt:4118–4145`, §IV.4 Lemma 5 p. 101 at
  `kob.txt:4222–4240`, Lemma 6 p. 102 at `kob.txt:4251–4302`.
- **[Gou20]** Gouvêa, 3rd ed.  Text `scratchpad …/refs/gouvea.txt`: Problem 343 at `gouvea.txt:11664`.
- **[LWX]** `.mathlib-quality/tate-riesz/references/lwx.txt:1807–1822`.

### The source proof, read in full ([Ked07, §2], `ked.txt:32–94`)

Definitions (§1, `ked.txt:19–29`):
> "Then form the lower convex hull of these points, i.e., take the intersection of every closed
> halfplane lying above some nonvertical line containing all the points. The boundary of this
> region is called the Newton polygon of `P`. Another way to represent the same data is to form
> the multiset consisting of the slopes of the polygon, each occurring with multiplicity equal to
> the width of the corresponding segment. The total cardinality is at most `n`, with equality if
> and only if `P₀ ≠ 0`; in case of a shortfall, we conventionally put in `+∞` as a slope with the
> missing multiplicity."

The claim (§2, `ked.txt:34–36`):
> "For untwisted polynomials, it was known to Newton (in the case `F = C((z))`) that for
> `P, Q ∈ F[T]`, the slope multiset of `PQ` is the union of the slope multisets of `P` and `Q`."

The sloped valuation (`ked.txt:42–48`):
> "For `r ∈ R`, define the sloped valuation function `v_r` on `F{T}` as
> `v_r(∑_i P_i T^i) = min_i {v(P_i) + ri}`. That is, `v_r` is the `y`-intercept of the supporting
> line of the Newton polygon of slope `r`."

Proposition 1 and its proof (`ked.txt:52–79`), untwisted case `h = 0`, `r₀ = +∞`:
> "Proposition 1 (Robba). For `r ≤ r₀` and `P, Q ∈ F{T}`, we have `v_r(PQ) = v_r(P) + v_r(Q)`.
> Proof. ... `v_r(PQ) ≥ min_{h,i,j} {v(P_{i+h}) + v(Q_j) + r(i + h + j)}`. (1)
> This immediately yields `v_r(PQ) ≥ v_r(P) + v_r(Q)`. To establish equality, let `i₀` and `j₀` be
> the smallest values of `i` and `j` which minimize `ri + v(P_i)` and `rj + v(Q_j)`, respectively;
> then (1) achieves its minimum for `h = 0`, `i = i₀`, `j = j₀` but not for any other `h, i, j` with
> `i + j = i₀ + j₀`. Hence `v_r(PQ) = v_r(P) + v_r(Q)`."

Corollary 2 and its proof (`ked.txt:85–90`):
> "Corollary 2. For `r < r₀`, the multiplicity of `r` as a slope of `PQ` is the sum of the
> multiplicities of `r` as a slope of `P` and `Q`. Proof. This follows from Proposition 1 and the
> fact that the left and right endpoints of the segment of slope `r` in the Newton polygon are the
> points where the support lines of slightly smaller and slightly larger slope, respectively,
> touch the polygon."

The textbook special case ([Kob84, §IV.4 Lemma 6, p. 102], `kob.txt:4256–4290`), whose proof is
the same mechanism written out:
> "Let `g(X) = (1 − cX) f(X) ∈ 1 + XΩ[[X]]`. Then the Newton polygon of `g(X)` is obtained by
> joining `(0, 0)` to `(1, λ)` and then translating the Newton polygon of `f(X)` by `1` to the right
> and `λ` upward. ... since `g(X) = (1 − X) f(X)`, we have `b_{i+1} = a_{i+1} − a_i` for `i ≥ 0`
> (with `a₀ = 1`), and so `ord_p b_{i+1} ≥ min(ord_p a_{i+1}, ord_p a_i)`, with equality holding if
> `ord_p a_{i+1} ≠ ord_p a_i` (by the isosceles triangle principle). Since both `(i, ord_p a_i)` and
> `(i, ord_p a_{i+1})` lie on or above the Newton polygon of `f(X)`, so does `(i, ord_p b_{i+1})`. If
> `(i, ord_p a_i)` is a vertex, then `ord_p a_{i+1} > ord_p a_i` and so `ord_p b_{i+1} = ord_p a_i`.
> This implies that the Newton polygon of `g(X)` must have the shape described in the lemma as far
> as the last vertex of the Newton polygon of `f(X)`. It remains to show that, in the case when the
> Newton polygon of `f(X)` has a final infinite slope `λ_f`, `g(X)` also does; and, if `f(X)`
> converges on `D(p^{λ_f})`, then so does `g(X)`."

### Plain-English proof (the source's argument, expanded to the height form)

Write `H_f, H_g, H_{fg}` for the heights of the three polygons (anchored at `0`), `s_f, s_g` for
the unit slopes, `M(n) = min_{i+j=n} (H_f(i) + H_g(j))` for the Minkowski height.

1. *Points above the sum* (Kedlaya's (1)): `c_n = ∑_{i+j=n} a_i b_j`, so by the ultrametric
   inequality `v(c_n) ≥ min (v(a_i) + v(b_j)) ≥ min (H_f(i) + H_g(j)) = M(n)`, using that each
   polygon lies below its points.
2. *Faces.*  For a real `σ`, the face of slope `σ` of a polygon with unbounded slopes is the
   interval `[i⁻, i⁺]` with `i⁻ = #{unit slopes < σ}`, `i⁺ = #{unit slopes ≤ σ}` (both finite);
   the polygon is the line of slope `σ` on the face, that line lies below the polygon everywhere
   and strictly below outside the face.  The endpoints are vertices, hence *points of the
   sequence* (a raised supporting line would contradict maximality — this is Kedlaya's "the points
   where the support lines of slightly smaller and slightly larger slope touch the polygon").
3. *Exactness at the endpoints* (Kedlaya's "smallest values `i₀`, `j₀` ... but not for any other"):
   at `m₁ = i⁻_f + i⁻_g` the split `(i⁻_f, i⁻_g)` is the unique minimiser of `H_f(i) + H_g(j)`,
   strictly, because moving `i` up costs at least `σ` per step in `f` while moving `j` down gains
   strictly less than `σ` per step in `g` (slopes before `i⁻_g` are `< σ`); so the term
   `a_{i⁻_f} b_{i⁻_g}` strictly dominates and `v(c_{m₁}) = M(m₁)`.  Same at `m₂ = i⁺_f + i⁺_g`
   with `≤`/`<` swapped.  `M` is the line of slope `σ` on `[m₁, m₂]`.
4. *Lower bound* `M(n) ≤ H_{fg}(n)`: take a minimising split `(i₀, j₀)` of `n`; comparing with its
   neighbours gives a common subgradient `σ` (`s_f(i₀−1), s_g(j₀−1) ≤ σ ≤ s_f(i₀), s_g(j₀)`); the
   line of slope `σ` through `(n, M(n))` is the sum of the two supporting lines, hence below `M`,
   hence below every point of `fg` (step 1), hence below `H_{fg}` (`line_le_height`).  If
   `M(n) = ⊤` then `fg` has no coefficients from `n` on and `H_{fg}(n) = ⊤`.
5. *Upper bound* `H_{fg}(n) ≤ M(n)`: with `σ` as in step 4, `n` lies on the face `[m₁, m₂]` of
   slope `σ` of the sum; `H_{fg}` is below the two exact points of step 3 and convex, so below the
   chord, which is `M` on `[m₁, m₂]`.
6. *Corollaries.*  Initial segment: if the first `n` slopes of `g` are `≤` all slopes of `f`, the
   split `(0, n)` minimises (pair the `i` slopes of `f` in a split `(i, n − i)` against the `i`
   slopes of `g` it displaces).  Multiplicities: `H_{fg} = M` has slope `σ` exactly on `[m₁, m₂]`
   and leaves it strictly on both sides, so `faceLeft_{fg} σ = m₁`, `faceRight_{fg} σ = m₂`.

## Prior-B2 log consultation (Step 4.6)

`.mathlib-quality/b2_log.jsonl`, 3 entries, read in full.
- `NewtonPolygon₀.unitSlope_cases` (2026-08-03T14:35Z) and its resolution (20:45Z): the degenerate
  one-point representation (`support = 1`, `lengths ≡ 0`, junk slope) — no name or shape match
  with any leaf, but **reason inherited**: junk unit slopes `⊤`/`⊥` on zero-width segments exist
  in `NewtonPolygon₀`.  Applied: every unit-slope statement of this board either allows `⊤`
  explicitly (`SlopesUnbounded`, faces, the Minkowski `⊤` case) or carries the `⊥`-exclusion
  `hb`/`unitSlope_ne_bot` (F02–F04, F07, F09, F11, F12, P02–P05, P09–P14).
- `LWX.exists_binomial_basis` (2026-09-03): characteristic-`p` / `ρ > 1` overshoot — unrelated
  (no name/shape match; this board is over a nontrivially normed field with no `char 0` or radius
  bound anywhere).

Verdict: clean of prior B2 history.

## Attack conventions

Each leaf group lists attacks by category: [1] counterexample search, [2] edge cases,
[3] hypothesis strength, [4] source drift, [5] discharge.  Every cited name in [5] was
verified by `#check` in a scratch file against the built project (probe files
`scratchpad …/lean/probe.lean`, `probe2.lean`, 2026-09-09) or read at the cited line.

---

## Result R1 — `IsEntireNewtonPolygonOf.height_mul` (`Product.lean:299`), the Minkowski formula

### Definitions

- **D1** `NewtonPolygon₀.SlopesUnbounded` — `Face.lean:57`
  ```lean
  def SlopesUnbounded : Prop := ∀ σ : ℝ, ∃ j : ℕ, (σ : WithBotTop ℝ) < P.unitSlope j
  ```
  Source: [Ked07, §1] "in case of a shortfall, we conventionally put in `+∞` as a slope with the
  missing multiplicity" (the junk `⊤` tail of a finite polygon counts as exceeding every `σ`);
  [Kob84, §IV.4 Lemma 5, p. 101] `kob.txt:4222–4226`: > "Let `b` be the least upper bound of all
  slopes of the Newton polygon of `f(X)` ... Then the radius of convergence is `p^b` (`b` may be
  infinite, in which case `f(X)` converges on all of `Ω`)" — unbounded slopes ⟺ entire.
  Attacks: [2] the constant series (`support = 0`, every unit slope `⊤`) satisfies it ✓; a
  polygon with a final ray of slope `σ₀` fails it at `σ = σ₀` ✓ (intended); [3] compared with
  `∀ σ, {j | unitSlope j ≤ σ}.Finite`: equivalent by monotonicity, the chosen form avoids
  `Set.Finite` and makes `faceLeft/faceRight` `sInf`s of nonempty sets.  SURVIVED.
- **D2** `NewtonPolygon₀.faceLeft`, **D3** `faceRight` — `Face.lean:63, 68`
  ```lean
  def faceLeft (σ : ℝ) : ℕ := sInf {j : ℕ | (σ : WithBotTop ℝ) ≤ P.unitSlope j}
  def faceRight (σ : ℝ) : ℕ := sInf {j : ℕ | (σ : WithBotTop ℝ) < P.unitSlope j}
  ```
  Source: [Ked07, proof of Cor. 2] "the left and right endpoints of the segment of slope `r` ...
  are the points where the support lines of slightly smaller and slightly larger slope,
  respectively, touch the polygon".  Lean ↔ source: with monotone unit slopes, the first index
  whose slope is `≥ σ` is the number of slopes `< σ` = the touching point of a slightly smaller
  slope; the first index with slope `> σ` is the number of slopes `≤ σ` = the touching point of a
  slightly larger slope.  Attacks: [2] `Nat.sInf ∅ = 0` junk when the set is empty — only
  possible without `SlopesUnbounded`, and every lemma reading the value assumes it; for the
  constant series both are `0` ✓; for `1 + pX` (slope `1`): `faceLeft 1 = 0`, `faceRight 1 = 1`,
  `faceLeft 2 = faceRight 2 = 1` ✓ by hand.  SURVIVED.
- **D4** `IsEntireNewtonPolygonOf` — `Face.lean:223` (structure extending `IsNewtonPolygonOf`
  with `starting_point_fst`, `unitSlope_ne_bot`, `slopesUnbounded`).  Attacks: [3] each field is
  consumed: anchor by every height-at-`ℕ` argument (`height_eq_bot_iff`), no-`⊥` by
  `toReal`-faithfulness (Height.lean's `toReal_unitSlope_le` is the only ⊥-tolerant lemma),
  unboundedness by the faces; none is implied by the others (spec-satisfying polygons with a `⊥`
  representation exist, see the B2 log).  SURVIVED.
- **D5** `NewtonPolygon₀.minkowskiHeight` — `Product.lean:69`
  ```lean
  def minkowskiHeight (n : ℕ) : WithBotTop ℝ :=
    (range (n + 1)).inf fun i => P.height i + Q.height (n - i)
  ```
  Source: Kedlaya's (1) read at a fixed `k = i + j`: `min_{i+j=k} {v(P_i) + v(Q_j)}` with the
  points replaced by the polygons — the Minkowski sum of two convex polygons is the infimal
  convolution of their height functions.  Attacks: [2] `n = 0` gives `height 0 + height 0` ✓
  (P01's `minkowskiHeight_zero`); `⊤` splits are harmless (`⊤` is the top of the `inf`); `⊥`
  never occurs for anchored polygons (P01's `minkowskiHeight_ne_bot`); [5] instances
  `AddCommMonoid`/`OrderTop`/`SemilatticeInf` on `WithBotTop ℝ` and `Finset.inf_le`,
  `le_inf_iff`, `inf_le_iff`, `exists_mem_eq_inf` verified by `#check`.  SURVIVED.

### Leaves — Face.lean (convexity)

- **F01** (leaf, mathlib) `heightFun_sub_eq_sum` — `Face.lean:79`.  Statement: the increment of
  `heightFun` over `[m, n)` is `∑_{Ico m n} toReal (unitSlope i)`.  Source: definition of the
  polygon as a broken line (Kedlaya §1 "lower convex hull", Koblitz p. 97 "convex polygonal
  line"); this is `Height.lean:681`'s private `heightFun_sub`, re-derived because `Height.lean` is
  read-only for this board.  Discharged by: `Finset.sum_Ico_eq_sub` + `heightFun` unfolding
  (2 lemmas).  Attacks: [2] `m = n` gives `0 = 0` ✓; [5] `Finset.sum_Ico_eq_sub` needs
  `AddCommGroup ℝ` ✓ (`#check`).  SURVIVED.
- **F02** (leaf, project) `line_le_height_of_unitSlope` — `Face.lean:87`.  Statement: if the unit
  slopes before `i₀` are `≤ σ` and from `i₀` on `≥ σ`, and `height i₀ = y`, then
  `y + σ(k − i₀) ≤ height k` for all `k`.  Source: [Ked07, §2] "`v_r` is the `y`-intercept of the
  supporting line of the Newton polygon of slope `r`" — the supporting line of slope `σ` touches
  where the slopes cross `σ`.  Lean ↔ source: the source's supporting line at slope `r` touches
  the polygon on the segment of slope `r`; our hypotheses say `i₀` lies on that segment (left
  slopes `≤ σ`, right slopes `≥ σ`, both non-strict so the endpoints and the interior qualify), and
  the conclusion is "the line lies on/below the polygon" at every integer, `⊤` heights included.
  Discharged by: F01, `toReal_unitSlope_le`-style faithfulness of `toReal` off `⊤`/`⊥`
  (`height_eq_heightFun`, `unitSlope_ne_top_of_height_ne_top`, `unitSlope_eq_top_of_height_eq_top`),
  `Finset.card_nsmul_le_sum` / `sum_le_card_nsmul`.  Attacks: [1] searched for a lemma
  contradicting the shape: `Height.lean:733` `height_le_chord` proves the dual chord bound, no
  contradiction; [2] `k = i₀` gives `y ≤ y` ✓; `k` in the `⊤` region: RHS `⊤` ✓; `i₀ = 0` reduces
  to `Height.lean:722` `le_heightFun` ✓ consistent; [3] `hb` needed: with a `⊥` unit slope
  `toReal ⊥ = 0` breaks `h₁`'s translation when `σ < 0` (see B2 inheritance); `hx` needed for
  `height k` at naturals to be the walked value; [4] no drift: the source statement is exactly
  "supporting line lies below".  SURVIVED.
- **F03** (leaves, project) `line_lt_height_of_unitSlope_lt`, `line_lt_height_of_lt_unitSlope` —
  `Face.lean:96, 106`.  Strict forms of F02 on the side where the slope comparison is strict.
  Source: [Kob84, Lemma 6 proof] "If `(i, ord_p a_i)` is a vertex, then `ord_p a_{i+1} > ord_p a_i`"
  — strict slope change gives strict inequality off the vertex.  Discharged by: the F02 argument
  with one strict term in the sum (`Finset.sum_lt_sum_of_nonempty`, `Ico` nonempty since `k < i₀`
  resp. `i₀ < k`).  Attacks: [2] `k = i₀ − 1` (one term, strict ✓); right-strict form when
  `unitSlope i₀ = ⊤`: `height k = ⊤` for `k > i₀`, strict ✓ (`⊤` is `>` every coercion); [3] the
  non-strict side of each hypothesis cannot be dropped (the sum needs a bound on every term).
  SURVIVED.
- **F04** (leaf, project) `height_eq_of_forall_unitSlope_eq` — `Face.lean:115`.  On a stretch of
  unit slopes `= σ` the height is the line.  Source: the polygon is a broken line (Kedlaya §1).
  Discharged by: `height_eq_heightFun`, `heightFun_succ` by induction on `k − i₀`
  (`SpecConstruction.lean:283` has the same telescoping privately).  Attacks: [2] `k = i₀` ✓;
  [3] no `hb`: the hypothesis pins every slope in range to a real; `hx` needed for the walk.
  SURVIVED.

### Leaves — Face.lean (faces)

- **F05** (leaves, mathlib) `SlopesUnbounded.exists_le`, `unitSlope_lt_of_lt_faceLeft`,
  `le_unitSlope_of_faceLeft_le`, `faceLeft_le_of_le_unitSlope`, `unitSlope_le_of_lt_faceRight`,
  `lt_unitSlope_of_faceRight_le`, `le_faceRight_of_forall_le`, `faceLeft_le_faceRight`,
  `faceRight_le_faceLeft_of_lt` — `Face.lean:124–164`.  Source: the D2/D3 quote (endpoints as
  touching points of nearby slopes) — these are the order-theoretic reading of "first index with
  slope `≥ σ` / `> σ`".  Discharged by: `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.notMem_of_lt_sInf`
  (verified `#check`), `unitSlope_mono` (`Height.lean:421`), `lt_of_lt_of_le`.  Attacks:
  [1] `faceLeft_le_faceRight` could fail if `<`-set were larger than `≤`-set — it is smaller, so
  `sInf` is larger ✓ direction checked; [2] `σ` below every slope: `faceLeft = faceRight = 0` ✓;
  `σ` equal to a slope of multiplicity `m` starting at `a`: `faceLeft = a`, `faceRight = a + m` ✓;
  [3] `hP` needed exactly where `sInf_mem` is used (the set must be nonempty), absent where only
  `notMem_of_lt_sInf`/`sInf_le` are used — checked per lemma.  SURVIVED.
- **F06** (leaves, project) `exists_height_faceLeft_eq`, `exists_height_faceRight_eq`,
  `height_eq_of_mem_face` — `Face.lean:170, 175, 180`.  Source: Cor 2's "segment of slope `r`"
  (a segment: finite heights, linear).  Discharged by: F05, `unitSlope_ne_top_of_height_ne_top`
  contrapositive (`unitSlope_eq_top_of_height_eq_top` + `height_eq_top_mono`), `height_eq_bot_iff`,
  F04.  Attacks: [2] degenerate face (`faceLeft = faceRight`): the linear statement is the
  identity at one point ✓; [3] `exists_height_*` need no `hP` (indices below the endpoint have
  slopes `< σ`/`≤ σ`, hence `≠ ⊤`, whichever `sInf` junk applies — if the set is empty the `sInf`
  is `0` and `height 0` is the anchor, finite ✓); `height_eq_of_mem_face` needs `hP` for the
  lower slope bound.  SURVIVED.
- **F07** (leaves, project) `faceLeft_line_le_height`, `faceLeft_line_lt_height`,
  `faceRight_line_le_height`, `faceRight_line_lt_height` — `Face.lean:188–210`.  F02/F03 at
  `i₀ = faceLeft σ` (slopes `< σ` before, `≥ σ` after) and `i₀ = faceRight σ` (`≤ σ` before, `> σ`
  after).  Source: Cor 2's touching support lines.  Discharged by: F02, F03, F05 (4 instantiations).
  Attacks: [5] hypothesis shapes match F02/F03 argument-for-argument (checked against the
  skeleton signatures).  SURVIVED.

### Leaves — Face.lean (spec consequences)

- **F08** (leaves, project) `starting_point_fst_eq_zero`, `height_zero_eq`,
  `height_ne_top_of_ne_top` — `Face.lean:237, 242, 247`.  Source: [Kob84, p. 97] the polygon
  "joining `(0, 0)` with `(n, ord_p a_n)` which passes on or below all of the points" (anchored at
  the first point; below the points).  Discharged by: `IsNewtonPolygonOf.start_mem`, `start_le`,
  `starting_point_fst_le` (`Spec.lean:84`), `height_le`, `pointHeight_coe`,
  `NewtonPolygon.height_startingPoint` (`Basic.lean:223`, through `height_toNewtonPolygon`).
  Attacks: [2] `v 0 = ⊤` (no constant term): `starting_point_fst_eq_zero` correctly demands
  `v 0 ≠ ⊤`; [3] `height_ne_top_of_ne_top` needs no anchor hypothesis (pure `height_le`).
  SURVIVED.
- **F09** (leaf, project) `height_eq_pointHeight_of_unitSlope_lt` — `Face.lean:256`.  Statement:
  where the unit slope strictly increases (`unitSlope i < unitSlope (i+1)`), `height (i+1)` is the
  point.  Source: [Kob84, §IV.3 p. 97] `kob.txt:4109–4110` > "By the vertices of the Newton
  polygon we mean the points `(i_j, ord_p a_{i_j})` where the slopes change." and [Ked07, Cor. 2
  proof] "the points where the support lines ... touch the polygon".  Lean ↔ source: the source
  *defines* vertices as points of the sequence; at the spec level this is a theorem: if the
  polygon were strictly below the point at a slope change, the supporting line of an intermediate
  slope, raised by a small `ε`, would still lie on/below every point (strictly below the polygon
  off `i + 1` by F03, with a margin growing linearly in the distance) and `line_le_height` would put
  it below the polygon at `i + 1`, contradiction.  Discharged by: F03 (both forms), F08,
  `IsNewtonPolygonOf.line_le_height` (`Support.lean:151`), `height_le`; `ε := min(δ, p − h)/2` with
  `δ := min(σ − s_i, s_{i+1} − σ)`.  Attacks: [1] searched `Spec.lean`/`SpecConstruction.lean` for
  a contradicting shape: `newtonPolygon₀OfSeq_height_vertex` (`SpecConstruction.lean:451`) proves
  the same fact for the constructed polygon in raw algorithm form — corroborates, no
  contradiction; [2] `unitSlope (i+1) = ⊤` (last vertex): take `σ := s_i + 1`; heights right of
  `i + 1` are `⊤`, so only the left inequality is needed ✓; `i + 1` inside a collinear stretch is
  excluded by the strict hypothesis ✓ (there the claim is false: `1 + X + X²` has `height 1 = 0`
  equal to the point, but `1 + pX + X²` has `height 1 = 0 < 1 = v(p)` and indeed no slope change at
  `1`); [3] `hb` needed (a `⊥` slope at `i` gives no real `σ`); the anchor `hx` is needed by
  `line_le_height`; [4] no drift — the source's "vertex" is exactly "slope changes", our
  `unitSlope i < unitSlope (i+1)`.  SURVIVED.
- **F10** (leaf, project) `height_eq_top_of_forall_eq_top` — `Face.lean:265`.  Statement: if
  `v k = ⊤` for all `k ≥ n` (`n ≥ 1`) then `height n = ⊤`.  Source: [Kob84, p. 97] the polygon of
  a polynomial ends at `(n, ord_p a_n)`; [Ked07, §1] the `+∞` convention past the last point.
  Lean ↔ source: the constructed polygon ends at the last point (`SpecConstruction.lean:642`,
  private `height_eq_top_of_tail`); at the spec level: if `height n` were a real `h`, the line of
  a large slope `σ` through `(n, h + 1)` lies on/below every point (finitely many finite points
  left of `n`, all `⊤` from `n` on), so `line_le_height` gives `h + 1 ≤ h`.  Discharged by:
  `line_le_height`, `Finset.exists_le`/`Finset.sup'` for `σ`, `pointHeight_eq_top_iff`.  Attacks:
  [2] `n = 0`: excluded by `0 < n` — correctly, since the anchor is a finite point (`start_mem`)
  and `v 0 = ⊤` is impossible; [3] no `hb` needed (no unit-slope arithmetic); [4] the source's
  "ends at `(n, ord a_n)`" is the `⊤` region of `height` per `Basic.lean:216` docstring ("to the
  right of a terminating polygon it is `⊤`").  SURVIVED.
- **F11** (leaf, project) `slopesUnbounded_of_forall_line` — `Face.lean:273`.  Statement: if for
  every real `σ` the points lie on/above some line of slope `σ`, the slopes are unbounded.
  Source: [Kob84, Lemma 5, p. 101] `kob.txt:4227–4232` > "First let `|x|_p < p^b`, i.e., `ord_p x > −b`.
  Say `ord_p x = −b'`, where `b' < b`. Then `ord_p(a_i x^i) = ord_p a_i − ib'`. But it is clear
  (see Figure 5) that, sufficiently far out, the `(i, ord_p a_i)` lie arbitrarily far above
  `(i, b'i)`" — the converse direction ("sup of slopes `= +∞` when the series is entire") is the
  same picture read backwards.  Lean ↔ source: if all unit slopes were `≤ σ`, then
  `height k ≤ height 0 + σ k` (F01/F02-style telescoping), while `line_le_height` at slope `σ + 1`
  gives `height k ≥ b + (σ + 1) k`, impossible for large `k`.  Discharged by: F01,
  `line_le_height`, `toReal_unitSlope_le`.  Attacks: [2] the constant series: all slopes `⊤`,
  conclusion immediate ✓; [3] `hb` needed (a `⊥` slope would make "all slopes `≤ σ`" possible with
  `toReal ⊥ = 0 > σ`); [4] Koblitz's Lemma 5 is stated for `radius = p^b`; we only use the entire
  direction, proved from the spec rather than from convergence — no drift in the claim.
  SURVIVED.
- **F12** (leaves, project) `height_faceLeft_eq_pointHeight`, `height_faceRight_eq_pointHeight` —
  `Face.lean:280, 286`.  Source: [Ked07, Cor. 2 proof] "the left and right endpoints ... are the
  points where the support lines ... touch the polygon".  Discharged by: F09 at `i + 1 = faceLeft σ`
  (`unitSlope (faceLeft σ − 1) < σ ≤ unitSlope (faceLeft σ)`, F05), F08 `height_zero_eq` when the
  endpoint is `0`; same for `faceRight` with `≤ σ < `.  Attacks: [2] endpoint `0` (anchor) ✓;
  `faceRight σ` with `unitSlope (faceRight σ) = ⊤` (last vertex) ✓ F09 handles `⊤`; [5] F09's
  hypothesis `unitSlope i < unitSlope (i + 1)` is produced by F05's two inequalities via
  `lt_of_lt_of_le` ✓.  SURVIVED.

### Leaves — Product.lean

- **P01** (leaves, mathlib) `minkowskiHeight_le`, `le_minkowskiHeight_iff`,
  `exists_minkowskiHeight_eq`, `minkowskiHeight_comm`, `minkowskiHeight_zero`,
  `minkowskiHeight_ne_bot`, `minkowskiHeight_eq_top_mono` — `Product.lean:75–103`.  Source: D5
  (the definition).  Discharged by: `Finset.inf_le`, `Finset.le_inf_iff`,
  `Finset.exists_mem_eq_inf` (nonempty `range (n+1)`), `Finset.mem_range`, `Finset.inf_range_*`
  reflection via `le_antisymm` + `le_inf_iff` for `comm`, `height_eq_bot_iff`,
  `height_eq_top_mono` (`Height.lean:556`), `WithBot.add_eq_top`-style case analysis.  Attacks:
  [2] `_eq_top_mono` at `m = n` ✓; the split `i > n` in the monotonicity proof uses `height_Q 0 ≠ ⊤`
  from the anchor — checked: `NewtonPolygon.height_startingPoint` gives the real anchor height;
  [3] `_ne_bot` and `_eq_top_mono` need both anchors (else a `⊥` height at a negative-anchor
  polygon breaks them) — minimal.  SURVIVED.
- **P02** (leaf, project) `subgradient_line_le_minkowskiHeight` — `Product.lean:111`.  Statement:
  the line of slope `σ` through `(i₀ + j₀, height_P i₀ + height_Q j₀)` lies below the Minkowski
  height when `σ` separates the slopes of `P` at `i₀` and of `Q` at `j₀`.  Source: Prop 1's (1)
  read with the polygons in place of the points, plus "`v_r` is the `y`-intercept of the
  supporting line": `v_σ(P ⊕ Q) = v_σ(P) + v_σ(Q)` is exactly "the supporting lines add".
  Discharged by: F02 twice, `le_minkowskiHeight_iff`, `WithBot.coe_add`.  Attacks: [2] `m = i₀ + j₀`:
  equality ✓; [3] uses only anchors and no-`⊥` (no unboundedness) — minimal, checked.  SURVIVED.
- **P03** (leaf, project) `exists_subgradient` — `Product.lean:124`.  Statement: a split
  `(i₀, n − i₀)` attaining a finite Minkowski height has a common real subgradient.  Source:
  expansion of [Ked07, Cor. 2 proof] ("the points where the support lines of slightly smaller and
  slightly larger slope touch"): the minimising split is where the two polygons have a common
  supporting slope.  Prose: compare with `(i₀ + 1, j₀ − 1)` and `(i₀ − 1, j₀ + 1)`: optimality gives
  `s_Q(j₀ − 1) ≤ s_P(i₀)` and `s_P(i₀ − 1) ≤ s_Q(j₀)`; take `σ := max(s_P(i₀ − 1), s_Q(j₀ − 1))`
  (real: both are `≠ ⊤` because `height_P i₀`, `height_Q j₀` are finite, `≠ ⊥` by `hb`); if
  `i₀ = 0` or `j₀ = 0` drop the missing term; if both are `0` take
  `σ := min(toReal s_P 0, toReal s_Q 0) − 1`.  Discharged by: `minkowskiHeight_le` at the two
  neighbouring splits, `unitSlope_eq_of_height_eq` (`Support.lean:44`) to read slopes as height
  increments, `unitSlope_mono`.  Attacks: [1] tried to break the conclusion at a split where
  `P` has slope `⊤` at `i₀` (`height_P (i₀+1) = ⊤`): then `σ ≤ ⊤` is free and the `Q` side gives the
  bound ✓; [2] `n = 0` handled by the last clause ✓; `i₀ = n` (all of `n` on `P`): only the `Q`
  lower bound is vacuous ✓; [3] "finite value" `y` is necessary (at a `⊤` Minkowski height there
  is no supporting line); [4] Kedlaya never states this lemma — it is the discrete KKT condition
  implicit in "the segment of slope `r` of the sum"; flagged as an *expansion*, not a quote.
  SURVIVED.
- **P04** (leaves, project) `minkowskiHeight_faceLeft`, `height_faceLeft_add_lt`,
  `minkowskiHeight_faceRight`, `height_faceRight_add_lt` — `Product.lean:141–166`.  Source:
  [Ked07, Prop. 1 proof] "let `i₀` and `j₀` be the smallest values of `i` and `j` which minimize
  ... then (1) achieves its minimum for `h = 0`, `i = i₀`, `j = j₀` but not for any other" (left
  endpoints; the right endpoints are the largest minimisers, same argument).  Lean ↔ source:
  Kedlaya's `i₀` (smallest minimiser of `ri + v(P_i)`) is our `faceLeft σ` once the endpoints are
  known to be points (F12); the "not for any other" is `height_faceLeft_add_lt`: for a split
  `(i, j)` with `i > faceLeft_P`, `height_P i ≥ line` (F07 `≤`) and `height_Q j > line` strictly
  (F07 `<`, since `j < faceLeft_Q`), and symmetrically.  Discharged by: F07 (4 lemmas), P02,
  `WithBot` order arithmetic.  Attacks: [2] `i = faceLeft_P` forces `j = faceLeft_Q` (excluded by
  `hne`) ✓; a split with `height_P i = ⊤`: strictly larger ✓ (`⊤` beats any coercion, and the
  face heights are finite by F06); [3] all six hypotheses are used (both faces need `hP`, `hQ`).
  SURVIVED.
- **P05** (leaf, project) `minkowskiHeight_eq_of_mem_face` — `Product.lean:175`.  On
  `[faceLeft_P + faceLeft_Q, faceRight_P + faceRight_Q]` the Minkowski height is the line of slope
  `σ`.  Source: Cor 2 ("the segment of slope `r`" of the sum has these endpoints).  Prose: `≥`
  by P02 at the left endpoints; `≤` by the explicit split `i := faceLeft_P + min(m − m₁,
  faceRight_P − faceLeft_P)`, `j := m − i`, both on their faces, where F06 gives the linear values.
  Discharged by: P02, F06 `height_eq_of_mem_face` twice, `minkowskiHeight_le`.  Attacks: [2]
  `m = m₁` ✓ (`hy`); `m = m₂` ✓ (`i = faceRight_P`, `j = faceRight_Q`); degenerate faces ✓;
  [5] `F05.faceLeft_le_faceRight` supplies `min` bookkeeping in `ℕ` — `omega`.  SURVIVED.
- **P06** (leaves, mathlib) `inf_negLogNorm_le_negLogNorm_sum`, `negLogNorm_sum_eq_of_forall_lt`,
  `pointHeight_eq_coe` — `Product.lean:195, 201, 222`.  Source: [Kob84, Lemma 6 proof]
  "`ord_p b_{i+1} ≥ min(ord_p a_{i+1}, ord_p a_i)`, with equality holding if
  `ord_p a_{i+1} ≠ ord_p a_i` (by the isosceles triangle principle)"; [Ked07, (1)].  Discharged by:
  `le_negLogNorm_add` (`NegLogNorm.lean:86`) by `Finset.induction`, or
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` + `negLogNorm_le_negLogNorm`;
  `IsNonarchimedean.apply_sum_eq_of_lt` (`Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean:227`)
  with `f := norm` (`IsUltrametricDist.isNonarchimedean_norm`, `norm_neg`) and
  `negLogNorm_lt_negLogNorm` (`NegLogNorm.lean:82`); `pointHeight` unfolding with
  `Algebra.algebraMap_self_apply`.  Attacks: [2] empty sum: `inf ∅ = ⊤ ≤ negLogNorm 0 = ⊤` ✓;
  singleton ✓; [3] `IsUltrametricDist K` is necessary (archimedean fields violate the bound);
  [5] the `#check`s confirm the exact hypothesis shapes (`hk : k ∈ s`,
  `hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)` — note the order is reversed relative to `negLogNorm`,
  bridged by `negLogNorm_lt_negLogNorm`).  These three are candidates for
  `ForMathlib/…/NegLogNorm.lean` and `Spec.lean` (relocation deferred, plan.md).  SURVIVED.
- **P07** (leaves, mathlib+project) `inf_coeffVal_add_le_coeffVal_mul`,
  `coeffVal_mul_eq_of_forall_lt` — `Product.lean:208, 215`.  Source: [Ked07, Prop. 1 proof]
  the display (1) at `h = 0` and "achieves its minimum ... but not for any other".  Discharged by:
  `PowerSeries.coeff_mul` (`antidiagonal`), `Finset.mem_antidiagonal`, `negLogNorm_mul`
  (`NegLogNorm.lean:132`, `NormMulClass` from the field), P06, and the reindexing
  `antidiagonal n ↔ range (n+1)` (`Finset.Nat.antidiagonal_eq_map`/`sum_antidiagonal_eq_sum_range_succ`).
  Attacks: [2] `n = 0` ✓ (`c₀ = a₀ b₀`, `negLogNorm_mul`); [3] `hi₀ : i₀ ≤ n` is needed for the
  term to exist; [4] Kedlaya's (1) has the extra twisted terms `h ≥ 0` — at `h = 0` it is verbatim
  our inequality.  SURVIVED.
- **P08** (leaves, project) `coeff_zero_ne_zero`, `starting_point_fst_mul`,
  `minkowskiHeight_le_pointHeight_mul` — `Product.lean:231, 237, 245`.  Source: [Kob84, Lemma 6
  proof] "Since both `(i, ord_p a_i)` and `(i, ord_p a_{i+1})` lie on or above the Newton polygon
  of `f(X)`, so does `(i, ord_p b_{i+1})`" — the points of the product lie above the sum.
  Discharged by: F08 (`start_mem`, `coeffVal_eq_top_iff`), `negLogNorm_mul` + `mul_ne_zero`,
  P07 + `height_le` (each `coeffVal ≥ height`) + `Finset.inf_mono`/`le_inf_iff` + `pointHeight_eq_coe`.
  Attacks: [2] `n = 0` ✓; [3] `minkowskiHeight_le_pointHeight_mul` needs only the two specs (no
  anchors) — checked, stated so.  SURVIVED.
- **P09** (leaf, project) `minkowskiHeight_le_height_mul` — `Product.lean:255` (≥ direction).
  Source: Cor 2 + Prop 1 assembled: the sum's supporting line of slope `σ` is below the points,
  hence below the polygon.  Prose in step 4 above.  Discharged by: P01 (`exists_minkowskiHeight_eq`,
  `minkowskiHeight_eq_top_mono`, `minkowskiHeight_zero`), P03, P02, P08, F10, F08
  (`starting_point_fst_mul`), `line_le_height` with `a := y − σ n`, `b := σ`.  Attacks: [2] the `⊤`
  case needs `n ≥ 1`: `minkowskiHeight_zero` is finite, so `M(n) = ⊤` forces `n ≥ 1` ✓; [3] uses no
  unboundedness — stated with the weaker hypotheses (an `IsEntire` bundle would be over-specified;
  attack 3 applied and the signature adjusted at planning time); [5] `line_le_height` needs
  `Pfg.starting_point.1 = 0` — supplied by `starting_point_fst_mul` ✓.  SURVIVED.
- **P10** (leaves, project) `pointHeight_mul_faceLeft`, `pointHeight_mul_faceRight` —
  `Product.lean:270, 279`.  Source: Prop 1's equality clause.  Discharged by: P07
  (`coeffVal_mul_eq_of_forall_lt`), P04 (strictness), F12 (the endpoints are points, so
  `coeffVal f (faceLeft σ) = height`), `height_le` for the other splits, `pointHeight_eq_coe`.
  Attacks: [2] both endpoints `0`: the split `(0, 0)` of `0` is unique ✓; [3] both `IsEntire`
  bundles are used in full (F12 needs all four fields).  SURVIVED.
- **P11** (leaf, project) `height_mul_le_minkowskiHeight` — `Product.lean:290` (≤ direction).
  Prose in step 5 above.  Discharged by: P01, P03, F05 (`faceLeft_le_of_le_unitSlope`,
  `le_faceRight_of_forall_le` to bracket `i₀`, `j₀`), P04, P05, P10, `height_le` (`hfg`),
  `height_le_chord` (`Height.lean:740`) with `x := m₁`, `z := m₂`, `a := M(m₁)`, `c := M(m₂)`
  (reals by F06/P04), `starting_point_fst_mul` for `hxs`.  Attacks: [2] `m₁ = m₂`: then `n = m₁`
  and the chord formula has `(c − a)/0 = 0` in Lean, giving `a` — consistent ✓; `M(n) = ⊤`:
  `le_top` ✓; [3] both `IsEntire` bundles needed (faces of both factors); [5] `height_le_chord`'s
  hypotheses `hxs : starting_point.1 ≤ x`, `hxy`, `hyz` are `omega` from the bracketing.
  SURVIVED.
- **P12** (assembly) `height_mul` — `Product.lean:299`.  `le_antisymm (P11) (P09)` (one line; P09
  is called with the projections of the bundles).  Source: [Ked07, §2] "the slope multiset of
  `PQ` is the union" in height form.  Attacks (composition): [1] the counterexample
  `(1 − X)∑Xⁱ = 1` — `∑ Xⁱ` violates `slopesUnbounded`, so the hypotheses exclude it ✓; with
  `f = ∑Xⁱ` (bounded) and `g = 1 − X` (unbounded) the formula fails, so the hypothesis is needed on
  *each* factor ✓ (both bundles are demanded); [2] `f = g = 1` ✓ (`M(n) = ⊤` for `n ≥ 1` = the
  point polygon); `f = 1 + X`, `g = 1 + pX`: `M = min(...)` gives the two-segment polygon of
  `1 + (1+p)X + pX²` with slopes `0, 1` ✓ by hand; [4] Kedlaya states Cor 2 for polynomials
  (`r < r₀ = +∞`); we generalise to unbounded-slope power series — a strict generalisation whose
  proof is the same, with Koblitz's Lemma 6 convergence caveat showing why rays must be excluded.
  SURVIVED.

### Corollaries

- **P13** (leaves, project) `height_mul_of_forall_le`, `unitSlope_mul_of_forall_le` —
  `Product.lean:310, 319`.  Source: [LWX, p. 25] `lwx.txt:1815–1818` > "By Proposition 2.15, one
  deduces that the set of all `U_p`-slopes on `S^D_{k+2}(K^pIw_{q²};ψ) ⊕ S^D_{k+2}(K^pIw_{q²};ψ⁻¹)`
  is exactly the set of the first `n_{k+1}` `U_p`-slopes in each of `S^{D,†}_{(k,ψ)}` and
  `S^{D,†}_{(k,ψ⁻¹)}`."  Lean ↔ source: LWX read "the classical slopes are the first `n_{k+1}`
  slopes of the whole space" off classicality; the formal content (the piece `lwx-theta` AG3
  isolated) is: the polygon of `F·G` agrees with that of `G` on `[0, n]` when the `n` slopes of `G`
  are at most every slope of `F`.  Prose: `M(n) ≤ H_f(0) + H_g(n)` (split `0`); for a split
  `(i, n − i)`, `i ≥ 1`, `H_f(i) − H_f(0) = ∑_{t<i} s_f(t) ≥ ∑_{t<i} s_g(n − i + t) = H_g(n) − H_g(n − i)`
  termwise by `hle`.  Slope form: from the height form at `j` and `j + 1` via
  `unitSlope_eq_of_height_eq`, `⊤` cases via `unitSlope_eq_top_of_height_eq_top`.  Discharged
  by: P12, P01, F01, `Finset.sum_le_sum`, `unitSlope_eq_of_height_eq`.  Attacks: [2] `n = 0`:
  `height 0 = height_f 0 + height_g 0` ✓ (`minkowskiHeight_zero`); [3] **`hn : Pg.height n ≠ ⊤` was
  in the draft and is over-specified**: if it fails, some unit slope of `g` below `n` is `⊤`, so
  `hle` makes every unit slope of `f` `⊤`, every `height_f i` (`i ≥ 1`) is `⊤`, and both sides are
  `height_f 0 + ⊤` — dropped from the skeleton on 2026-09-09; [4] the LWX sentence is about
  eigenvalue slopes of a direct sum; our statement is the polygon-level identity that, with S3's
  factorisation, yields it — recorded on `lwx-theta` as the intended consumer.  SURVIVED (after
  the fix).
- **P14** (leaves, project) `slopesUnbounded_mul`, `mul`, `faceRight_mul`, `faceLeft_mul` —
  `Product.lean:328–351`.  Source: [Ked07, Cor. 2] (quoted above); [Gou20, Problem 343]
  > "Let `f(X)` and `g(X)` both be pure polynomials of slope `m`. Show that their product is also
  > pure of slope `m`." (the special case `faceLeft m = 0`, `faceRight m = deg`).  Prose in step 6.
  Discharged by: P12, P04, P05, F05, F07, P01 (`exists_minkowskiHeight_eq` for the finite-min
  strictness), `unitSlope_eq_of_height_eq`, `unitSlope_mono`.  Attacks: [2] `σ` below every
  slope of both: `0 = 0 + 0` ✓; `σ` above every slope of both (finite polygons): `deg fg = deg f +
  deg g` ✓ (Kedlaya's "total cardinality ... with equality iff `P₀ ≠ 0`"); [3] `hbfg` is needed to
  read `Pfg`'s unit slopes from its heights; `slopesUnbounded_mul` does not need it (it is a
  statement about heights growing faster than `σ`: `M(m₂ + 1) > M(m₂) + σ` then
  `unitSlope_eq_top_of_height_eq_top` or the increment) — signature checked.  SURVIVED.
- **P15** (leaves, project) `slopesUnbounded_newtonPolygon₀OfPowerSeries`,
  `isEntireNewtonPolygonOf_coeffVal`, `isNewtonPolygonOf_coeffVal_mul` — `Product.lean:366, 373,
  380`.  Source: [Kob84, Lemma 5] (entire ⟺ slopes unbounded) and the Gauss bound
  `‖a_k‖ cᵏ ≤ ‖f‖_c` (the affine floor of slope `log c`, exactly `CoeffVal.lean:114`'s argument).
  Discharged by: F11 with `PowerSeries.le_gaussNorm` at `c = exp σ` (as in
  `isAdmissible_coeffVal_of_isRestricted`, `CoeffVal.lean:116`), `isNewtonPolygonOf_powerSeries`
  (`SpecConstruction.lean:764`), `isAdmissible_coeffVal_of_isRestricted`, `exists_coeffVal_ne_top`,
  F08 `starting_point_fst_eq_zero`, `newtonPolygon₀OfSeq_unitSlope_ne_bot` (`Support.lean:90`),
  `PowerSeries.isRestricted.mul` (`Restricted/Basic.lean:76`), `mul_ne_zero`.  Attacks:
  [2] polynomials: `Polynomial.isRestricted_toPowerSeries` supplies `hf` ✓; the constant series ✓;
  [3] `∀ c > 0, IsRestricted c f` is the project's `IsEntire` unfolded (`TateFredholm/Entire.lean:107`),
  taken unbundled so `NewtonPolygons` does not import `TateFredholm`; `hf0` is needed for the
  anchor.  SURVIVED.
- **P16** (leaves, project) `height_newtonPolygon₀OfPowerSeries_mul`,
  `height_newtonPolygon₀OfPowerSeries_mul_of_forall_le`,
  `unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`,
  `faceRight_newtonPolygon₀OfPowerSeries_mul` — `Product.lean:388–422`.  Instantiations of
  P12–P14 at the constructed polygons via P15; the `a₀ = 1` forms use
  `newtonPolygon₀_starting_point_of_coeff_zero_eq_one` (`CoeffVal.lean:155`) to read `height 0 = 0`
  (`NewtonPolygon.height_startingPoint`).  Attacks: [3] the `_of_forall_le` height form needs
  `= 1` (to cancel `height_f 0`), the slope form only `≠ 0` — signatures checked accordingly.
  SURVIVED.
- **P17** (leaf, project) `height_newtonPolygon₀OfPowerSeries_coe_natDegree_ne_top` —
  `Product.lean:432`.  F08 `height_ne_top_of_ne_top` at the leading coefficient
  (`Polynomial.leadingCoeff_ne_zero`, `Polynomial.coeff_coe`, `isNewtonPolygonOf_coeffVal_coe`
  `CoeffVal.lean:138`).  Attacks: [2] `G` constant: `natDegree = 0`, anchor ✓.  SURVIVED.
- **P18** (leaf, project; MILESTONE) `height_newtonPolygon₀OfPowerSeries_mul_coe` —
  `Product.lean:441`.  P16's `_of_forall_le` at `g := (G : PowerSeries K)`, `n := G.natDegree`,
  with `Polynomial.coeff_coe` for `hg0` and `Polynomial.isRestricted_toPowerSeries` for `hg`.
  Source: [LWX, p. 25] as in P13, in the shape `lwx-theta` S3 produces
  (`charPowerSeries u = charPowerSeries (u * (1 − pr)) * G`, `G : R[X]`).  Attacks: [4] the LWX
  consumer needs the polygon of `det(1 − Tu)` at `n_{k+1} = deg G`; the hypothesis `hle` is what
  L2.3/L2.4 of `lwx-theta` supply (classical slopes `≤ k + 1 ≤` non-classical slopes; ties
  allowed by `≤`) ✓ shape matches; [2] `G = 1`: `natDegree 0`, trivial ✓.  SURVIVED.

## Confidence gate (Step 5)

1. Every leaf discharged from mathlib or project code (cited above) — no API gap remains: the
   only genuinely new mathematics is the spec-level "vertices are points" (F09) and "`⊤` beyond the
   last point" (F10), both reduced to `line_le_height`.  ✓
2. Skeleton compiles (`lake build PhD.NewtonPolygons.Product`, sorry warnings only).  ✓
3. Every leaf has a verbatim quote (Kedlaya/Koblitz/Gouvêa/LWX) or is marked as an expansion
   with its parent quote (P03), plus a Lean ↔ source paragraph.  ✓
4. Every leaf and both internal nodes (P12, and D5's composition) carry an attack log with ≥ 3
   categories; one attack succeeded (P13's `hn`) and was fixed in the skeleton.  ✓
5. Prior-B2 log checked; reason inherited into the `⊥`/`⊤` hygiene.  ✓
6. Tree mirrors the source: Prop 1 (1) → P06/P07/P08; Prop 1 equality → P04/P10; Cor 2's
   endpoints → D2/D3, F05–F07, F12; Cor 2's conclusion → P14; Koblitz Lemma 6 → the same chain
   for one linear factor.  LOC anchors: Kedlaya's (1) is a 3-line display → P07 ≈ 60 LOC;
   Prop 1's equality clause 4 lines → P10 ≈ 50 LOC; Cor 2's proof 3 lines → P14 ≈ 120 LOC (the
   sentence packs the face bookkeeping); Koblitz's Lemma 6 proof 25 lines → F09 ≈ 60 LOC.  ✓
7. Single conclusion per declaration: no `∧` in any skeleton conclusion; `IsEntireNewtonPolygonOf`
   is a structure (documented bundle), `mul` its assembly.  ✓

No REVIEW-PENDING leaves.  Gate passes.
