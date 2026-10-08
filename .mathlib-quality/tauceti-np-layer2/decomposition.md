# Decomposition for Newton polygons, Layer 2 (the polygon of a polynomial and of a power series)

Board `.mathlib-quality/tauceti-np-layer2/`. Specification `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`,
Layer 2 ([RM]). Every leaf below is a `sorry`-bodied declaration of the skeleton (file:line from
`scratch/sorries.py`, 2026-10-06), with: **Q** the verbatim source passage (a labelled quote from the
list below, or the roadmap clause); **M** the Lean ↔ source match; **D** the discharge (Mathlib /
[L0] / [L1] / [RAG] names, all elaborated in `scratch/names_pre.lean` or `scratch/signatures.txt`;
"[SRC] File.decl" = the Main-chain proof read for ideas); **A** the attacks attempted, by category
([1] counterexample search in [L0]/[L1]/Mathlib for the negation or a contradicting statement, [2]
edge cases, [3] hypothesis strength, [4] source drift, [5] discharge check), ending in the verdict.
Sizes cite the source line count where the source has one.

## Skeleton location

`PhD/TauCeti/Code/NewtonPolygons/Coeff/{NormedAddValuation, Generic, CoeffVal, PowerSeries, Polynomial,
Extension, SupportValue, GaussNorm, Pure, Distinguished, Padic, Examples}.lean` — 256 open declarations,
261 `sorry`s (`scratch/sorries.json`); `lake build PhD.TauCeti` passes with `sorry` warnings only
(3654 jobs, 2026-10-06); every signature elaborates (`scratch/signatures.txt`, 0 errors).

## Verbatim source passages (labels used by the leaves)

- **[Q-Kob-def]** [Kob84] IV §3 p. 97 (`koblitz.txt:4200–4210`): *"Let f(X) = 1 + Σ a_i X^i ∈ 1 + XΩ[X] be
  a polynomial of degree n with coefficients in Ω and constant term 1. Consider the following sequence
  of points in the real coordinate plane: (0, 0), (1, ord_p a_1), (2, ord_p a_2), …, (i, ord_p a_i), …,
  (n, ord_p a_n). (If a_i = 0, we omit that point, or we think of it as lying "infinitely" far above the
  horizontal axis.) The Newton polygon of f(X) is defined to be the "convex hull" of this set of points,
  i.e., the highest convex polygonal line joining (0, 0) with (n, ord_p a_n) which passes on or below all
  of the points (i, ord_p a_i)."*
- **[Q-Kob-vert]** [Kob84] p. 97 (`koblitz.txt:4219–4222`): *"By the vertices of the Newton polygon we
  mean the points (i_j, ord_p a_{i_j}) where the slopes change. If a segment joins a point (i, m) to
  (i', m'), its slope is (m' − m)/(i' − i); by the "length of the slope" we mean i' − i, i.e., the length
  of the projection of the corresponding segment onto the horizontal axis."*
- **[Q-Kob-ps]** [Kob84] IV §4 pp. 98–99 (`koblitz.txt:4259–4290`): *"Now let f(X) = 1 + Σ a_i X^i ∈
  1 + XΩ[[X]] be a power series. … The Newton polygon of f(X) is defined to be the "limit" of the Newton
  polygons of the f_n(X). More precisely, we follow the same recipe as in the construction of the
  Newton polygon of a polynomial: plot all of the points (0, 0), (1, ord_p a_1), …, (i, ord_p a_i), …;
  rotate the vertical line through (0, 0) until it hits a point (i, ord_p a_i), then rotate it about the
  farthest such point it hits, and so on. But we must be careful to notice that three things can
  happen: (1) We get infinitely many segments of finite length. … (2) At some point the line we're
  rotating simultaneously hits points (i, ord_p a_i) which are arbitrarily far out. In that case, the
  Newton polygon has a finite number of segments, the last one being infinitely long. … (3) … we let
  the last segment of the Newton polygon have slope equal to the least upper bound of all possible
  slopes for which it passes below all of the (i, ord_p a_i)."*
- **[Q-Kob-degen]** [Kob84] p. 99 (`koblitz.txt:4297–4303`): *"A degenerate case of possibility (3)
  occurs when the vertical line through (0, 0) cannot be rotated at all without crossing above some
  points (i, ord_p a_i). For example, this is what happens with f(X) = Σ X^i/p^{i²}. In that case, f(X)
  is easily seen to have zero radius of convergence, i.e., f(x) diverges for any nonzero x. In what
  follows we shall exclude that case from consideration and shall suppose that f(X) has a nontrivial
  disc of convergence."*
- **[Q-Kob-L5]** [Kob84] Lemma 5, pp. 100–101 (`koblitz.txt:4339–4352`): *"Let b be the least upper bound
  of all slopes of the Newton polygon of f(X) = 1 + Σ a_i X^i ∈ 1 + XΩ[[X]]. Then the radius of
  convergence is p^b (b may be infinite, in which case f(X) converges on all of Ω). PROOF. First let
  |x|_p < p^b, i.e., ord_p x > −b. Say ord_p x = −b', where b' < b. Then ord_p(a_i x^i) = ord_p a_i − ib'.
  But it is clear (see Figure 5) that, sufficiently far out, the (i, ord_p a_i) lie arbitrarily far
  above (i, b'i), in other words, ord_p(a_i x^i) → ∞, and f(X) converges at X = x. Now let |x|_p > p^b,
  i.e., ord_p x = −b' < −b. Then we find in the same way that ord_p(a_i x^i) = ord_p a_i − b'i is
  negative for infinitely many values of i. Thus f(x) does not converge."*
- **[Q-Kob-shear]** [Kob84] p. 101 (`koblitz.txt:4364–4371`): *"If c ∈ Ω, ord_p c = λ, and g(X) = f(X/c),
  then the Newton polygon for g is obtained from that for f by subtracting the line y = λx — the line
  through (0, 0) with slope λ — from the Newton polygon for f. This is because, if f(X) = 1 + Σ a_i X^i and
  g(X) = 1 + Σ b_i X^i, then we have ord_p b_i = ord_p(a_i/c^i) = ord_p a_i − λi."*
- **[Q-Gou-def]** [Gou20] §7.4 p. 251 (`gouvea.txt:11270–11300`): *"So let f(X) ∈ K[X] be a polynomial. Since
  we are mostly interested in understanding the zeros of f(X) we may as well factor out any powers of
  X which divide f(X). In other words, we may assume that f(0) ≠ 0. Then, dividing through by f(0), we may
  also assume that f(0) = 1. … On a set of axes, we plot the points (0,0) and, for each i between 1 and n,
  (i, v_p(a_i)). (There is one caveat: if a_i = 0 for some i, it is not clear what v_p(a_i) is to be; we
  just take it to be +∞, and think of the point as "infinitely high." In practice this just means that
  we ignore that value of i.) The polygon we want to consider is, in fancy terms, the lower boundary of
  the convex hull of this set of points."*
- **[Q-Gou-feat]** [Gou20] p. 252 (`gouvea.txt:11320–11333`): *"i) the slopes of the line segments appearing
  in the polygon — we will call these the "Newton slopes" of f(X); ii) the "length" of each slope, by
  which we mean the length of the projection of the corresponding segment on the x-axis; iii) the
  "breaks," i.e., the values of i such that the point (i, v_p(a_i)) is a vertex of the polygon. …
  Notice that the sum of all the lengths will always be equal to the degree, and that (0,0) and
  (n, v_p(a_n)) will always be vertices. It is also clear from the "rotating line" construction that
  the slopes will form an increasing sequence."*
- **[Q-Gou-P340]** [Gou20] Problem 340, p. 254 (`gouvea.txt:11363–11366`): *"It might be useful to
  generalize the definition in order to remove the condition f(0) = 1, and just assume f(0) ≠ 0. How
  would the definition change? What would be the relation between the polygons of f(X) and of af(X)
  (for a ∈ K^×)?"*
- **[Q-Gou-first]** [Gou20] p. 254 (`gouvea.txt:11377–11404`): *"Let's look at the first segment of the
  Newton polygon. If this segment has slope m, it connects the point (0,0) to some other point (i, mi).
  (So that the first Newton slope is m, and it has length i.) … First, it means that there are no points
  below the line y = mx; in other words, v_p(a_j) ≥ mj for every j. Second, the point (i, mi) itself tells
  us that v_p(a_i) = mi. Third, the fact that there is a break tells us that the subsequent points are
  really above the line; in other words, v_p(a_j) > mj if j > i. Translating from valuations to absolute
  values, we get • |a_j| ≤ p^{−mj} = (p^{−m})^j for all j, which we can rewrite as |a_j|(p^m)^j ≤ 1 for
  all j, • |a_i| = p^{−mi}, which we can rewrite as |a_i|(p^m)^i = 1, and • |a_j| < p^{−mj} if j > i, which
  we can rewrite as |a_j|(p^m)^j < 1 if j > i. If we now let c = p^m, we can read these conditions in terms
  of the c-norm. They say: • ‖f(X)‖_c = 1, and • i is the largest integer such that ‖f(X)‖_c = |a_i|c^i.
  In other words, the fact that the first break is at (i, mi) means that if we take c = p^m then
  ‖f(X)‖_c = 1 and i is the distinguished number that appears in Proposition 7.2.3."*
- **[Q-Gou-D741]** [Gou20] Definition 7.4.1 and the following remark, p. 255 (`gouvea.txt:11410–11427`):
  *"A polynomial f(X) ∈ K[X] is called pure if its Newton polygon has only one slope. If this slope is
  m, we will say f(X) is pure of slope m. … In fact, we can go further, by noticing that a polynomial
  h(X) = 1 + b_1X + b_2X² + ⋯ + b_nX^n will be pure of slope m, according to the discussion above, exactly
  when it has the property that, for c = p^m, ‖f(X)‖_c = |b_n|c^n = 1, i.e., the maximum occurs at the
  end and is equal to 1. Problem 341 Prove that a polynomial h(X) = 1 + b_1X + ⋯ + b_nX^n is pure of
  slope m if and only if we have ‖f(X)‖_{p^m} = |b_n|p^{mn} = 1."*
- **[Q-Gou-P723]** [Gou20] Proposition 7.2.3, p. 235 (`gouvea.txt:10596–10604`): *"Let c > 0 be some real
  number, and ‖‖ = ‖‖_c. Let f(X) = a_0 + a_1X + a_2X² + ⋯ + a_nX^n be a polynomial in K[X], and suppose
  that there exists an integer N such that 0 < N < n for which we have ‖f(X)‖ = |a_N|c^N and
  ‖f(X)‖ > |a_j|c^j for any j > N."*
- **[Q-Gou-second]** [Gou20] pp. 258–259 (`gouvea.txt:11505–11536`): *"• |a_j|c^j ≤ p^{(m'−m)i} for all j,
  • the equality holds for j = k, and • the inequality is strict for j > k. In other words, we get, for
  c = p^{m'}, that ‖f(X)‖_c = p^{(m'−m)i} (and notice that since m' > m this is bigger than 1) and that k
  is the distinguished number in Proposition 7.2.3 (i.e., the maximum is realized at the degree k
  term)."*
- **[Q-Gou-ps]** [Gou20] p. 260 (`gouvea.txt:11585–11592`): *"The definition is formally identical: given a
  power series of the form f(X) = 1 + a_1X + a_2X² + ⋯ + a_nX^n + ⋯ we plot the points (i, v_p(a_i)) for
  i = 0, 1, 2, …, ignoring, as before, any points where a_i = 0. The Newton polygon of f(X) is again
  obtained by the "rotating line" procedure."*
- **[Q-Gou-ex1]** [Gou20] p. 261 (`gouvea.txt:11640–11660`): *"Take the power series f(x) = 1/(1−pX) = 1 +
  pX + p²X² + p³X³ + ⋯ + p^nX^n + ⋯ The points (i, v_p(a_i)) are just (0,0), (1,1), (2,2), (3,3), …, (i,i), …
  We are in the first case above, and the polygon comes out to be a line of slope one which contains
  infinitely many points."*
- **[Q-Gou-ex2]** [Gou20] p. 262 (`gouvea.txt:11672–11684`): *"We have already seen an example of a series
  whose Newton polygon falls into case (ii) above: f(X) = 1 + pX + pX² + pX³ + ⋯ + pX^n + ⋯ In this case,
  the Newton polygon is a horizontal line … Checking the special case shows that if |x| = 1, then the
  series does not converge."*
- **[Q-Gou-L748]** [Gou20] Lemma 7.4.8, p. 264 (`gouvea.txt:11757–11790`): *"Let m be the sup of the slopes
  appearing in the Newton polygon of a series f(X) = 1 + a_1X + a_2X² + ⋯ (so that m is either a number
  or is +∞). Then the radius of convergence of the series is p^m … Now superpose the line y = bx on the
  Newton polygon of the series (see Figure 7.8). Since the slope of the polygon eventually becomes
  larger than b, the polygon eventually passes and then gets farther and farther above the line
  y = bx. The points (i, v_p(a_i)) are on or above the polygon, so it follows that v_p(a_i) − bi → ∞ as
  i → ∞, and the series converges."*
- **[Q-Gou-L749]** [Gou20] Lemma 7.4.9, pp. 265–266 (`gouvea.txt:11793–11830`): *"i) If the polygon ends in
  an infinite segment of slope m which contains infinitely many of the points (i, v_p(a_i)), then the
  region of convergence is the open ball of radius p^m. … the series will converge at a point x with
  |x| = p^m if we have lim |a_i| p^{mi} = 0, or, in valuation notation, if v_p(a_i) − mi goes to infinity
  as i goes to infinity. This would mean that the points in our polygon get arbitrarily far above the
  line y = mx. But that clearly cannot happen."*
- **[Q-Ked-def]** [Ked07] §1 p. 1 (`kedlaya-newton-poly.txt`, page 1): *"Draw the points in R² given by
  {(−i, v(f_i)) : i = 0, …, n, P_i ≠ 0}. Then form the lower convex hull of these points, i.e., take the
  intersection of every closed halfplane lying above some nonvertical line containing all the points.
  The boundary of this region is called the Newton polygon of P. Another way to represent the same data
  is to form the multiset consisting of the slopes of the polygon, each occurring with multiplicity
  equal to the width of the corresponding segment. The total cardinality is at most n, with equality
  if and only if P_0 ≠ 0."* ⚠ Kedlaya's abscissa is `−i`; this roadmap's is `i` (convention 6), so his
  slopes are the negatives of ours and his `v_r` is our supporting value at the slope `−r`.
- **[Q-Ked-vr]** [Ked07] §2 p. 2: *"For r ∈ R, define the sloped valuation function v_r on F{T} as
  v_r(Σ_i P_i T^i) = min_i {v(P_i) + ri}. That is, v_r is the y-intercept of the supporting line of the
  Newton polygon of slope r. Note that for P ∈ F{T}, the function r ↦ v_r(P) is continuous."*
- **[Q-Ked-C2]** [Ked07] proof of Corollary 2, p. 2: *"the left and right endpoints of the segment of slope
  r in the Newton polygon are the points where the support lines of slightly smaller and slightly
  larger slope, respectively, touch the polygon".*
- **[Q-BGR-521]** [BGR] 5.2.1/1 (as transcribed on the rigid-analytic-geometry Layer 0 board): *"A
  strictly convergent power series g = Σ_{ν=0}^∞ g_ν(X₁, …, X_{n−1}) Xₙ^ν is Xₙ-distinguished of degree s
  if (1) g_s is a unit in T_{n−1} and (2) |g_s| = |g| and |g_s| > |g_ν| for all ν > s."*
- **[Q-RM-intro]** [RM] Layer 2 introduction: *"It carries a normed additive valuation: an additive
  valuation v : AddValuation K (WithTop Γ), a strictly monotone additive map e : Γ →+ ℝ, and a base b > 1
  with ‖x‖ = b ^ (-(e (v x))) for x ≠ 0. Prove that the three members of Layer 1's family are instances:
  (normAddValZ K, Int.cast, ‖π‖⁻¹) for a discretely valued K with uniformiser π, (normAddValQ K π,
  Rat.cast, ‖π‖⁻¹) in the commensurable case, and (normAddVal K, id, exp 1) always."*
- **[Q-RM-2.1.2]** [RM] §2.1.2: *"for a slope m and the radius c = b ^ m, the term ‖aₖ‖ cᵏ is at most 1
  exactly when the point (k, e (v aₖ)) lies on or above the line of slope m through the origin, and
  similarly for <, =, and for comparison against another term rather than against 1. State the whole
  dictionary; the later layers use every direction of it."*
- **[Q-RM-2.2.8]** [RM] §2.2.8: *"the polygons of f for (v, e, b) and for (v', e', b') on the same normed
  field differ by the positive scalar log b' / log b in height, because both e (v x) and e' (v' x) equal
  -log ‖x‖ up to that scalar. In particular the polygon for normAddValZ on ℚ_p is the polygon for
  normAddVal divided by log p."*

Other [RM] clauses are quoted inline where a leaf is pure bookkeeping the textbooks do not state.

## Prior-B2 log consultation (Step 4.6)

`.mathlib-quality/b2_log.jsonl` (root, 8 entries), `tauceti-np-layer0/` (no log), `tauceti-np-layer1/b2_log.jsonl`
(empty), this board's (empty). The only polygon entry is `NewtonPolygon₀.unitSlope_cases` (2026-08-03): a
phantom zero-width real-sloped segment of the legacy segment-decorated structure, "resolved — real-slope
phantom now unrepresentable". No leaf below matches it by name; by shape, every unit slope here is
Layer 0's derived `unitSlope h j = h (j+1) - h j` on the height function (Layer 0 design decision 1), so
the defect cannot recur. The seven LWX entries concern modular forms. **Verdict: every leaf is clean of
prior B2 history.**

---

## §2 introduction — `NormedAddValuation.lean` (L1)

### Plain-English proof substrate

[Q-RM-intro] is the specification; Layer 1 supplies the three valuations and their norm-recovery
theorems (`normAddVal_apply_of_ne_zero`: `normAddVal K x = -log ‖x‖`; `normAddValZ_eq_iff_of_isUniformizer`:
`normAddValZ K x = k ↔ ‖x‖ = ‖π‖ ^ k`; `norm_eq_norm_rpow_normAddValQ`: `‖x‖ = ‖π‖ ^ q`). The term
dictionary [Q-RM-2.1.2] is [Q-Gou-first]'s translation *"|a_j| ≤ p^{−mj} … which we can rewrite as
|a_j|(p^m)^j ≤ 1"* done once for an arbitrary element: `‖x‖ (b^m)^k = b^{-e(v x)} b^{mk} = b^{mk - e(v x)}`,
and `b^t ≤ 1 ↔ t ≤ 0` for `b > 1`; the `⊤` cases are `x = 0`. The scalar relation [Q-RM-2.2.8] is two
logarithms of the same `‖x‖`.

### Leaves

- **L1.1–L1.6** `map_zero`, `map_one`, `map_mul`, `map_pow`, `map_inv`, `min_le_map_add` — Q: [RM]
  "an additive valuation v : AddValuation K (WithTop Γ)". M: the `AddValuation` axioms restated through
  `CoeFun` (`coe_apply` is `rfl`). D: `AddValuation.map_zero`, `map_one`, `map_mul`, `map_pow`, `map_inv`
  (`WithTop Γ` is a `LinearOrderedAddCommGroupWithTop`), `map_add`. A: [2] `x = 0` in `map_inv`: `0⁻¹ = 0`,
  `-(⊤) = ⊤` (`LinearOrderedAddCommGroup.neg_top`) ✓. [3] nothing to weaken. [5] all six names elaborate.
  SURVIVED.
- **L1.7–L1.8** `eq_top_iff`, `ne_top_iff` — Q: [RM] convention 5 "⊤ is the only junk value … `⊤` exactly at a
  vanishing coefficient" (§2.1.1). M: `v x = ⊤ ↔ x = 0` on a field. D: `AddValuation.top_iff`
  (`[Nontrivial (WithTop Γ)]` ✓), `AddValuation.ne_top_iff`. A: [2] trivial `Γ`: `WithTop Γ` still
  nontrivial ✓. [3] a field is needed (`top_iff` is false over `ℤ` with the `p`-adic valuation? no — true;
  false over a ring with zero divisors), which the layer assumes. SURVIVED.
- **L1.9** `exists_eq_coe` — Q: same. M: `x ≠ 0 → ∃ γ, v x = ↑γ`. D: `WithTop.ne_top_iff_exists`, L1.8. A: [2]
  `x = 1`: `γ = 0` ✓. SURVIVED.
- **L1.10–L1.11** `base_pos`, `log_base_pos` — Q: [RM] "a base b > 1". M: `0 < b`, `0 < log b`. D:
  `one_lt_base`, `zero_lt_one.trans`, `Real.log_pos`. SURVIVED ([5] names elaborate).
- **L1.12** `norm_eq_rpow` — Q: [RM] "‖x‖ = b ^ (-(e (v x))) for x ≠ 0". M: the structure field with the
  value `γ` of `v x` named. D: `norm_eq_rpow'`. A: [3] `x ≠ 0` is encoded as `v x = ↑γ` (L1.8); [4] exact.
  SURVIVED.
- **L1.13** `embed_eq_neg_logb` — Q: [RM] conventions 2 ("`e (v x)` … equal `-log ‖x‖` up to that scalar")
  and 11; [Kob84] III §2 `ord_p a = -log_p |a|_p` (Layer 1's quote). M: `e γ = -log_b ‖x‖`. D: L1.12,
  `Real.logb_rpow` (`0 < b`, `b ≠ 1`), `neg_neg`. A: [2] `‖x‖ = 1`: `e γ = 0` ✓ (`Real.logb_one`). [5]
  `Real.logb_rpow` elaborates. SURVIVED.
- **L1.14** `norm_add_le_max` — Q: [RM] Layer 2 introduction "K is a nonarchimedean normed field throughout";
  Layer 1's [BGR] 1.5.2 dictionary. M: the strong triangle inequality derived from `min_le_map_add`. D:
  L1.6, L1.12, `Real.rpow_le_rpow_left_iff` (`1 < b`), cases `x + y = 0`, `x = 0`, `y = 0` (`norm_zero`,
  `le_max_left/right`). A: [2] `x + y = 0`: `0 ≤ max` ✓; [3] this is a theorem, not an extra assumption on
  `K` — it shows the layer needs no `IsUltrametricDist` (plan decision 1). SURVIVED. (~25 LOC.)
- **L1.15** `rpow_logb` — Q: [RM] §2.1.2 "the radius c = b ^ m" (every positive radius is such a power). M:
  `b ^ logb b c = c`. D: `Real.rpow_logb (base_pos) (one_lt_base).ne' hc`. SURVIVED.
- **L1.16–L1.18** `embedTop_top`, `embedTop_coe`, `embedTop_eq_top_iff` — Q: [RM] convention 4 "The points
  live in WithTop Γ, pushed into WithTop ℝ along e". M: `WithTop.map e` on `⊤` and on `↑γ`. D:
  `WithTop.map_top`, `WithTop.map_coe`, `WithTop.map_eq_top_iff`. SURVIVED ([2] `γ = 0`: `e 0 = 0` ✓).
- **L1.19–L1.20** `embedTop_strictMono`, `embedTop_le_embedTop` — Q: [RM] convention 2 "a strictly monotone
  additive map e". M: `WithTop.map` of a strictly monotone map is strictly monotone; `≤` reflects. D:
  `WithTop.strictMono_map_iff.mpr v.strictMono_embed`, `StrictMono.le_iff_le`. A: [3] strict monotonicity
  of `e` is exactly what makes `embedTop` injective and order-reflecting; monotone alone would not
  (collapsing `Γ`). SURVIVED.
- **L1.21** `embedTop_add` — Q: [RM] §1.1.4 "pushing v along mapAddHom' f pushes v.addVal along f"
  (additivity of the pushed values). M: `map e (a + b) = map e a + map e b` in `WithTop`. D:
  `WithTop.map_add` (`[AddHomClass]` for `Γ →+ ℝ`). A: [2] `a = ⊤`: `⊤ + b = ⊤ ↦ ⊤ = ⊤ + _` ✓
  (`WithTop.top_add`). SURVIVED.
- **L1.22–L1.23** `embedTop_apply_eq_top_iff`, `embedTop_map_one` — M: `⊤ ↔ x = 0`; `map e (v 1) = 0`. D: L1.18,
  L1.7; L1.2, L1.17, `map_zero` of `e`, `WithTop.coe_zero`. SURVIVED.
- **L1.24** `norm_mul_rpow_pow_eq_rpow` — Q: [Q-Gou-first] "|a_j| ≤ p^{−mj} … |a_j|(p^m)^j ≤ 1" (the term as a
  power of the base); [SRC] `CoeffVal.norm_mul_exp_pow_eq_exp` (`‖a‖ exp(m)^k = exp(log‖a‖ + mk)`). M:
  `‖x‖ (b^m)^k = b^(mk - e γ)` for `v x = γ`. D: L1.12, `Real.rpow_natCast`, `Real.rpow_mul` (`0 ≤ b`),
  `Real.rpow_add (base_pos)`, `mul_comm`, `sub_eq_neg_add`. A: [2] `k = 0`: `‖x‖ = b^{-eγ}` ✓ L1.12; `m = 0`:
  `‖x‖ · 1 = b^{-eγ}` ✓. [4] [SRC] has `exp` base and `log‖a‖`; the `(v, e, b)` form replaces `log ‖a‖` by
  `-e γ`, identical by L1.13. SURVIVED. Source: one line of [Gou20]; ~10 LOC.
- **L1.25–L1.27** `norm_mul_rpow_pow_le_one_iff`, `_lt_one_iff`, `_eq_one_iff` — Q: [Q-RM-2.1.2], [Q-Gou-first]
  (the three bullets). M: `‖x‖ (b^m)^k ≤ 1 ↔ ↑(mk) ≤ embedTop (v x)` etc.; for `x = 0` both sides read
  `0 ≤ 1`/`↑(mk) ≤ ⊤` (true), `0 < 1`/`↑(mk) < ⊤` (true), `0 = 1`/`⊤ = ↑(mk)` (false). D: L1.24, L1.9, L1.7,
  `Real.rpow_le_one_iff_of_pos`? — rather `Real.rpow_le_rpow_left_iff (one_lt_base)` after writing
  `1 = b ^ 0` (`Real.rpow_zero`), `sub_nonpos`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`, `WithTop.coe_inj`,
  `le_top`, `WithTop.coe_lt_top`, `norm_zero`, `zero_lt_one`. A: [1] the Layer-1 board's `normAddVal`
  statements are the `b = exp 1` case and agree in sign (`‖x‖ = exp(-r)`). [2] checked the three `x = 0`
  cases above; `k = 0`, `m` negative ✓ (no positivity of `m` used). [3] no hypothesis on `x` — the `⊤`
  bookkeeping is the point of stating it this way ([RM] "every direction of it"). [4] [Q-Gou-first] has
  the three directions for `p^m`; [RM] generalises `p` to `b`. SURVIVED. (~15 LOC each.)
- **L1.28–L1.30** `norm_mul_rpow_pow_le_iff`, `_lt_iff`, `_eq_iff` — Q: [Q-RM-2.1.2] "and for comparison
  against another term rather than against 1"; [Q-Gou-second] "|a_j|c^j ≤ p^{(m'−m)i} … equality holds for
  j = k … strict for j > k" (comparison of the term at `j` with the term at `i`). M: `‖x‖c^k ≤ ‖y‖c^j ↔
  embedTop (v y) + ↑(m (k − j)) ≤ embedTop (v x)`: the point `(k, e(v x))` is on or above the line of
  slope `m` through `(j, e(v y))`. Cases: `y = 0`: LHS `‖x‖c^k ≤ 0 ↔ x = 0`, RHS `⊤ ≤ _ ↔ embedTop (v x) = ⊤
  ↔ x = 0` ✓; `x = 0, y ≠ 0`: both true (`0 ≤ _`, `_ ≤ ⊤`); both nonzero: real inequality
  `mk − eγ ≤ mj − eγ' ↔ eγ' + m(k − j) ≤ eγ` ✓; `_lt`: `y = 0` both false, `x = 0 ≠ y` both true ✓;
  `_eq`: `x = y = 0` both true, one zero both false ✓. D: L1.24, L1.9, L1.7, `Real.rpow_le_rpow_left_iff`,
  `Real.rpow_lt_rpow_left_iff`, `Real.rpow_right_injective`-style (`Real.rpow_left_injective` is absent —
  use `(Real.rpow_le_rpow_left_iff hb).antisymm`-free route: `le_antisymm_iff` on both sides),
  `WithTop.coe_add`, `WithTop.top_add`, `WithTop.add_top`, `mul_sub`, `norm_nonneg`,
  `Real.rpow_pos_of_pos`. A: [2] the five zero-pattern cases above, `k = j` (`m · 0`), `m < 0` ✓. [3] no
  hypotheses. [4] [Q-Gou-second]'s comparison is against the term at the previous break; the Lean form
  takes arbitrary `j, k`. SURVIVED. (~25 LOC each.)
- **L1.31** `scale_pos` — Q: [Q-RM-2.2.8] "the positive scalar log b' / log b". M: `0 < log b / log b'`. D:
  L1.11, `div_pos`. SURVIVED.
- **L1.32** `embed_eq_scale_mul_embed` — Q: [Q-RM-2.2.8] "because both e (v x) and e' (v' x) equal -log ‖x‖ up
  to that scalar". M: `e' γ' = (log b / log b') · e γ` from `‖x‖ = b^{-eγ} = b'^{-e'γ'}`. D: L1.12 twice,
  `Real.log_rpow (base_pos)`, `Real.log_injOn_pos`-free: apply `Real.log` to both sides (`congrArg`),
  `Real.log_rpow`, then `field_simp` with L1.11. A: [2] `x = 1`: `0 = scale · 0` ✓. [3] the scalar is
  `log b / log b'` with `b, b' > 1` — nonzero denominators ✓. [4] [RM] writes "log b' / log b" for the
  factor from `(v,e,b)` to `(v',e',b')`; the computation gives `log b / log b'` (plan D9); checked on
  `ℚ_p`: `b = p`, `b' = e` gives `log p`, matching "[the polygon for normAddValZ] is the polygon for
  normAddVal divided by log p". SURVIVED.
- **L1.33** `embedTop_apply_eq_map` — M: the `WithTop` form of L1.32 with the `⊤` case. D: L1.32, L1.9,
  L1.7, `WithTop.map_top`, `WithTop.map_coe`. A: [2] `x = 0`: `⊤ = map _ ⊤` ✓. SURVIVED.
- **L1.34** `ofNormAddVal` (fields `one_lt_base`, `norm_eq_rpow'`) — Q: [Q-RM-intro] "(normAddVal K, id,
  exp 1) always". M: base `exp 1 > 1`; `normAddVal K x = ↑γ → ‖x‖ = (exp 1)^(-γ)`. D: `Real.one_lt_exp_iff`
  (`0 < 1`); `NormedField.normAddVal_eq_top` (so `x ≠ 0`), `normAddVal_apply_of_ne_zero` (`γ = -log ‖x‖`),
  `WithTop.coe_inj`, `Real.exp_one_rpow`, `Real.exp_log (norm_pos_iff.mpr hx)`, `neg_neg`. A: [2] `x = 1`:
  `γ = 0`, `(exp 1)^0 = 1 = ‖1‖` ✓. [5] both Layer-1 names in `signatures`/[L1]. SURVIVED.
- **L1.35** `ofNormAddVal_apply_of_ne_zero` — D: `normAddVal_apply_of_ne_zero` (the `CoeFun` unfolds by
  `rfl`). SURVIVED.
- **L1.36** `ofNormAddValZ` (fields `strictMono_embed`, `one_lt_base`, `norm_eq_rpow'`) — Q: [Q-RM-intro]
  "(normAddValZ K, Int.cast, ‖π‖⁻¹) for a discretely valued K with uniformiser π". M: `Int.cast` strictly
  monotone; `1 < ‖π‖⁻¹` since `0 < ‖π‖ < 1`; `normAddValZ K x = ↑d → ‖x‖ = (‖π‖⁻¹)^(-(d:ℝ))`. D:
  `Int.cast_strictMono`; `one_lt_inv_iff₀` with `‖π‖ < 1` from `hπ` (`Valuation.IsUniformizer.iff`:
  `v π = generator`, `Valuation.IsRankOneDiscrete.generator_lt_one`, `NormedField.valuation_apply`,
  `NNReal.coe_lt_coe`) and `0 < ‖π‖` (`generator_ne_zero`-style: `Units.ne_zero`); the norm:
  `NormedField.normAddValZ_eq_iff_of_isUniformizer` (`‖x‖ = ‖π‖ ^ d`, `zpow`), `inv_zpow'`,
  `Real.rpow_intCast`, `Real.rpow_neg (norm_nonneg _)`. A: [2] `x = π`: `d = 1`, `(‖π‖⁻¹)^(-1) = ‖π‖` ✓.
  [3] `hπ` is exactly Layer 1's hypothesis; `IsRankOneDiscrete` is the instance. [4] exact. SURVIVED.
- **L1.37** `ofNormAddValZ_apply_isUniformizer` — Q: [RM] §1.3.2 "addValZ v π = 1". D:
  `NormedField.normAddValZ_isUniformizer`. SURVIVED.
- **L1.38** `scale_ofNormAddValZ_ofNormAddVal` — Q: [Q-RM-2.2.8] "the polygon for normAddValZ on ℚ_p is the
  polygon for normAddVal divided by log p". M: `scale = log (‖π‖⁻¹) / log (exp 1) = -log ‖π‖`. D:
  `Real.log_inv`, `Real.log_exp`, `div_one`. SURVIVED ([2] on `ℚ_p`, `‖p‖ = p⁻¹` gives `log p`, L11.6).
- **L1.39** `ofNormAddValQ` (fields) — Q: [Q-RM-intro] "(normAddValQ K π, Rat.cast, ‖π‖⁻¹) in the
  commensurable case". M: `Rat.cast` strictly monotone; `1 < ‖π‖⁻¹` from `0 < v π < 1`
  (`Valuation.IsCommensurable.val_pos`, `val_lt_one`, `NormedField.valuation_apply`); `normAddValQ K π x =
  ↑q → ‖x‖ = (‖π‖⁻¹)^(-(q:ℝ))`. D: `Rat.cast_strictMono`; `one_lt_inv_iff₀`;
  `NormedField.norm_eq_norm_rpow_normAddValQ` (`‖x‖ = ‖π‖ ^ (q:ℝ)`), `Real.inv_rpow (norm_nonneg _)`,
  `Real.rpow_neg`, `inv_inv`. A: [2] `x = π`: `q = 1` (`normAddValQ_self`) ✓. SURVIVED.
- **L1.40** `ofNormAddValQ_self` — D: `NormedField.normAddValQ_self`. SURVIVED.

Internal node (the structure itself): could the fields be inconsistent (no model)? L1.34/36/39 are
three models. Could `CoeFun` lose information? It does not need to be injective (two bundles may share
`v`); `FunLike` was rejected for that reason (plan decision 1). SURVIVED.

---

## Generic polygon transforms — `Generic.lean` (L2)

### Plain-English proof substrate

Three transports and two facts about segments, none in [L0]. (i) Shifting right by `n`
([Q-RM] §2.2.7 "the polygon of X^n · f is translated right by n"): the shifted sequence is `⊤` on
`[0, n)` and `v (k − n)` beyond; convexity, the minorant property and maximality transport along
`k ↦ k + n` in both directions, a competitor `g` for the shifted sequence pulling back to `k ↦ g (k + n)`
for the original one. (ii) Reflecting in `[0, d]` ([RM] §2.2.7 "the polygon of Polynomial.reverse f is
the reflection i ↦ h (d − i)") for a sequence that is `⊤` beyond `d`: the unit slopes reverse and negate,
a competitor `g` for the reflected sequence reflects back to a competitor `k ↦ g (d − k)` on `[0, d]`,
`⊤` beyond (allowed because the original is `⊤` there). (iii) Scaling heights by `c > 0` ([Q-RM-2.2.8]):
`WithTop.map (c * ·)` preserves `⊤`, multiplies unit slopes by `c`, and a competitor rescales by `c⁻¹`.
(iv) [Q-Kob-vert]: a segment joins two consecutive vertices, "its slope is (m' − m)/(i' − i)"; for a
polygon with finitely many slopes every slope index lies between the last vertex at or before it (the
anchor is a vertex, `isVertex_anchor`) and the first vertex after it (the last finite index is a vertex,
`isVertex_of_succ_eq_top`). Each transport is proved through `IsNewtonPolygonOf` and
`IsNewtonPolygonOf.eq_newtonPolygon`, never through the walk ([RM] §0.2.4).

### Leaves

- **L2.1** `isAdmissible_of_finite` — Q: [RM] §0.2.3 "it holds for every sequence on or above a single
  line"; §2.1.3 "the coefficient valuation sequence of a polynomial is admissible". M: finite support ⟹
  a horizontal line below the finitely many values. D: `Set.Finite.bddBelow` on the image
  `(fun k ↦ (v k).untop₀) '' finiteSupport v`, `NewtonPolygon.isAdmissible_of_line` with `σ = 0` and
  `y` the lower bound (for `k` with `v k = ⊤`, `_ ≤ ⊤`; else `WithTop.coe_untop₀_of_ne_top`). A: [2] empty
  support: any line ✓ (admissibility is `∀ i, v i ≠ ⊤ → …`, vacuous). [3] finiteness cannot be dropped
  (`v k = -k²`, `not_isAdmissible_neg_sq`). SURVIVED. (~15 LOC.)
- **L2.2–L2.5** `shiftRight_add`, `shiftRight_of_le`, `shiftRight_of_lt`, `shiftRight_zero` — M: unfold
  `shiftRight`. D: `if_pos`/`if_neg`, `Nat.add_sub_cancel`, `Nat.le_add_left`, `funext`,
  `Nat.sub_zero`, `zero_le`. SURVIVED.
- **L2.6** `unitSlope_shiftRight` — M: `unitSlope (shift n h) (k + n) = unitSlope h k`. D: `unitSlope_nat`,
  L2.2 twice (`k + 1 + n = (k + n) + 1`, `Nat.add_right_comm`). SURVIVED.
- **L2.7** `isConvexSeq_shiftRight_iff` — M: convexity transports. D: `NewtonPolygon.isConvexSeq_iff_midpoint`
  on both sides (midpoint form: `h (k+1) + h (k+1) ≤ h k + h (k+2)`): for `k + 2 ≤ n` the shifted
  midpoint inequality is `⊤ + ⊤ ≤ ⊤ + _` or `_ ≤ ⊤ + _` ✓ (`WithTop.top_add`, `le_top`); for `k ≥ n` it
  is the original at `k − n`; the order-connectedness of the finiteness set transports along `· + n`
  (`finiteSupport` of the shift is the image under `(· + n)`, `Set.OrdConnected` of an image under an
  order embedding — via `Set.OrdConnected.image`-free direct proof with `mem_finiteSupport`). A: [2]
  `n = 0`: L2.5 ✓; `h ≡ ⊤` ✓. [5] `isConvexSeq_iff_midpoint` elaborates (needs
  `[IsSuccArchimedean ℕ]` ✓). SURVIVED. (~40 LOC.)
- **L2.8** `isNewtonPolygonOf_shiftRight_iff` — M: the three fields transport. D: L2.7, `le_points` by cases
  on `n ≤ k` (L2.3/L2.4, `le_top`); `greatest`: (→) given the shifted spec and a competitor `g` for `v`,
  `shiftRight n g` is a competitor for the shifted sequence (L2.7, pointwise), so `shiftRight n g ≤
  shiftRight n h`, read at `k + n` (L2.2); (←) a competitor `g` for the shifted sequence gives
  `g' k := g (k + n)`, convex (`isConvexSeq_iff_midpoint` transports; order-connectedness of a preimage
  under `· + n`), `≤ v` (L2.2), hence `≤ h`, so `g (k+n) ≤ h k = shiftRight n h (k + n)`; for `k < n`,
  `shiftRight n h k = ⊤` ✓. A: [1] could the shifted polygon have a point before `n`? No: `le_points`
  forces `⊤` there. [2] `n = 0` ✓; `v ≡ ⊤` ✓ (`h ≡ ⊤`). [3] no admissibility needed for the `iff`.
  SURVIVED. (~60 LOC.)
- **L2.9** `isAdmissible_shiftRight_iff` — D: `isAdmissible_iff_exists_line` on both sides: `y + σk ≤ v k`
  ↔ `(y − σn) + σk ≤ shiftRight n v k` (for `k < n` the right side is `≤ ⊤`; for `k ≥ n` substitute
  `k = k' + n`). A: [2] `n = 0` ✓. SURVIVED. (~25 LOC.)
- **L2.10** `newtonPolygon_shiftRight` — D: `isNewtonPolygonOf_newtonPolygon` (via
  `exists_isConvexMinorant_iff_isAdmissible`) for `v`, L2.8 (→), `IsNewtonPolygonOf.eq_newtonPolygon`.
  A: [3] admissibility needed only to have the polygon of `v` (the junk-free side). SURVIVED. (~8 LOC.)
- **L2.11–L2.13** `reflect_of_le`, `reflect_of_lt`, `reflect_reflect` — M: unfold; for `k ≤ d`,
  `d − (d − k) = k` (`Nat.sub_sub_self`); for `k > d`, both sides are `⊤` by `hv`. D: `if_pos`, `if_neg`,
  `Nat.sub_le`, `Nat.sub_sub_self`. A: [2] `d = 0`: `reflect 0 v = (v 0, ⊤, ⊤, …)` ✓. [3] `hv` is needed
  for `reflect_reflect` (otherwise the values beyond `d` are lost). SURVIVED.
- **L2.14** `unitSlope_reflect` — M: `unitSlope (reflect d h) k = −unitSlope h (d − (k+1))` for `k < d`.
  D: `unitSlope_nat`, L2.11 twice (`k + 1 ≤ d`), `LinearOrderedAddCommGroup.coe_sub`, `coe_neg`,
  `top_sub`, `sub_top`, `neg_top`, `neg_sub`, cases on `h (d − k)`, `h (d − (k+1))` being `⊤`
  (`WithTop.ne_top_iff_exists`). A: [2] one endpoint `⊤`: `⊤ − x = ⊤ = −(⊤)` and `x − ⊤ = ⊤ = −(⊤)` ✓
  (checked both `WithTop` group-instance rules). SURVIVED. (~25 LOC.)
- **L2.15** `IsConvexSeq.reflect` — M: convexity of the reflection of a convex sequence supported in
  `[0, d]`. D: `isConvexSeq_iff_midpoint`: for `k + 2 ≤ d` the reflected midpoint inequality is the
  original at `d − (k+2)` (`add_comm`); for `k + 1 ≥ d` a `⊤` appears on the right (L2.12 or `hd`);
  order-connectedness: the finiteness set of the reflection is `{k ≤ d | h (d−k) ≠ ⊤}`, the image of
  `finiteSupport h ∩ Iic d` under the antitone bijection `d − ·`, hence an interval (`Set.OrdConnected`
  by two points and `Nat.sub_le_sub_left`). A: [2] `d = 0` ✓. [3] `hd` is needed: a point beyond `d`
  would be lost and the reflected finiteness set might still be an interval, but L2.16 needs `hd`
  regardless. SURVIVED. (~60 LOC.)
- **L2.16** `IsNewtonPolygonOf.reflect` — M: the three fields. D: L2.15 (with `hd` for `h`: from `hv` and
  `le_points`, `h k = ⊤` beyond `d` — `top_le_iff`); `le_points` pointwise (L2.11, L2.12); `greatest`:
  a competitor `g` for `reflect d v` gives `g' := reflect d g`, convex by L2.15 **provided** `g` is `⊤`
  beyond `d` — it need not be! Use instead `g'' k := if k ≤ d then g (d − k) else ⊤`, which is
  `reflect d g` by definition (L2.11/L2.12 do not require `g` to vanish beyond `d`): `reflect d g` is
  convex (L2.15 applied to the *restriction* `Set.Iic d |>.piecewise g ⊤`, convex by
  `IsConvexSeq.piecewise_top` with `Set.ordConnected_Iic`, which is `⊤` beyond `d`), `≤ v` (for `k ≤ d`,
  `g (d−k) ≤ reflect d v (d−k) = v k`; for `k > d`, `⊤ ≤ v k` by `hv`), hence `≤ h`, so for `k ≤ d`
  `g k = reflect d g (d − k) ≤ h (d − k) = reflect d h k` and for `k > d` `reflect d h k = ⊤` ✓. A: [1] the
  attack above (a competitor finite beyond `d`) succeeded against the naive proof and the leaf's route
  was corrected to the piecewise restriction; the statement is unchanged. [2] `d = 0`: `v` a single point
  (or none) ✓. SURVIVED. (~70 LOC.)
- **L2.17** `newtonPolygon_reflect` — D: `hv` ⟹ `finiteSupport v ⊆ Iic d` finite (`Set.finite_Iic`,
  `Set.Finite.subset`) ⟹ L2.1 ⟹ `isNewtonPolygonOf_newtonPolygon` ⟹ L2.16 ⟹ `eq_newtonPolygon`. A: [2]
  `v ≡ ⊤`: both sides `⊤` ✓. SURVIVED.
- **L2.18–L2.20** `scaleHeight_eq_top_iff`, `finiteSupport_scaleHeight`, `unitSlope_scaleHeight` — D:
  `WithTop.map_eq_top_iff`; `Set.ext` with it; cases on `h k`, `h (k+1)` (`WithTop.map_top`, `map_coe`,
  `coe_sub`, `top_sub`, `sub_top`, `mul_sub`). A: [2] `c = 0`: `map (0 * ·)` sends finite values to `0`,
  still finite ✓ (no positivity needed for these three). SURVIVED.
- **L2.21** `isConvexSeq_scaleHeight_iff` (`0 < c`) — D: `IsConvexSeq` unfolds to order-connectedness
  (L2.19) and `MonotoneOn (unitSlope _)`; L2.20 and `WithTop.map` of `c * ·` is an order embedding for
  `c > 0` (`WithTop.strictMono_map_iff.mpr (strictMono_mul_left_of_pos hc)`, `.le_iff_le`). A: [3] `c > 0`
  is necessary: `c < 0` reverses slopes (`v k = k²` becomes `-k²`, not convex). SURVIVED.
- **L2.22** `isNewtonPolygonOf_scaleHeight_iff` (`0 < c`) — D: L2.21; `le_points` via the order
  embedding; `greatest`: a competitor `g` for the scaled sequence rescales by `c⁻¹` to a competitor for
  `v` (`scaleHeight c⁻¹ (scaleHeight c g) = g`, `inv_mul_cancel₀`), and conversely. A: [2] `c = 1` ✓.
  SURVIVED. (~40 LOC.)
- **L2.23** `isAdmissible_scaleHeight_iff` — D: `isAdmissible_iff_exists_line`: `y + σk ≤ v k ↔ cy + cσk ≤
  c · v k` (`WithTop.map_coe`, `mul_le_mul_left hc`); conversely scale by `c⁻¹`. SURVIVED. (~20 LOC.)
- **L2.24** `newtonPolygon_scaleHeight` — D: spec of `v`, L2.22, `eq_newtonPolygon`. SURVIVED.
- **L2.25** `slopeMultiset_scaleHeight` — D: `slopeMultiset` unfolds (`dif_pos` with `hfin` and the equal
  `slopeIndices` by L2.20 + `WithTop.map_eq_top_iff`), `Multiset.map_map`, `WithTop.untop₀` of
  `map (c * ·)` is `c * untop₀` (cases). A: [2] `hfin` fails: both sides junk `0`? then the statement
  needs `hfin` ✓ carried. SURVIVED. (~25 LOC.)
- **L2.26** `exists_isSegment_of_mem_slopeIndices` — Q: [Q-Kob-vert] "vertices … the points where the slopes
  change", [Q-Gou-feat] "(0,0) and (n, v_p(a_n)) will always be vertices". M: a slope index of a convex
  sequence with finitely many slopes lies in `[a, b)` for consecutive vertices `a ≤ j < b`. D: `h j ≠ ⊤`,
  `h (j+1) ≠ ⊤` (`mem_slopeIndices_iff`); the finiteness set is an interval `[anchor h, d]` with `d` the
  largest index (`Set.Finite.bddAbove` on `slopeIndices` gives the last slope index `j₁`, `d = j₁ + 1`,
  `h (d+1) = ⊤` since `d ∉ slopeIndices`); `a := sSup {i ≤ j | IsVertex h i}` (nonempty: `isVertex_anchor`,
  `anchor_le`; bounded; `Nat.sSup_mem`), `b := sInf {i | j < i ∧ IsVertex h i}` (nonempty: `d` is a vertex
  by `isVertex_of_succ_eq_top`, `j < d`; `Nat.sInf_mem`); consecutiveness from `Nat.le_sSup`/`Nat.sInf_le`.
  A: [1] [L0] has no such lemma (searched `IsSegment` lemmas: only `unitSlope_eq_of_isSegment`,
  `eq_add_nsmul_of_isSegment`). [2] `j = anchor`: `a = anchor` ✓; `j = d − 1`: `b = d` ✓; a polygon with one
  segment ✓. [3] `hfin` is used only to produce the right vertex; for a ray there may be none (the roadmap's
  `⌈k√2⌉` example) — the hypothesis is necessary. SURVIVED. (~60 LOC.)
- **L2.27** `IsConvexSeq.unitSlope_eq_div_of_isSegment` — Q: [Q-Kob-vert] "its slope is (m' − m)/(i' − i)".
  M: `unitSlope h j = (h b − h a)/(b − a)` on the segment. D: `IsConvexSeq.unitSlope_eq_of_isSegment` (the
  unit slope is constant `= unitSlope h a` on `[a, b)`), `IsConvexSeq.eq_add_nsmul_of_isSegment` at `k = b`
  (`h b = h a + (b − a) • unitSlope h a`), both `h a`, `h b` finite (`IsVertex`), `WithTop.coe_nsmul`,
  `nsmul_eq_mul`, `eq_div_iff` (`(b : ℝ) − a ≠ 0` from `a < b`, `Nat.cast_sub`, `sub_pos`). A: [2] `b = a + 1`:
  `unitSlope h a = h (a+1) − h a` ✓ (`unitSlope_nat`). [5] both [L0] names elaborate. SURVIVED. (~25 LOC.)

Internal nodes: the three transports are each "spec ⟹ spec ⟹ uniqueness"; could the children hold and
the parent fail? Only if `newtonPolygon` of the transformed sequence were junk, which `IsNewtonPolygonOf`
excludes. SURVIVED.
---

## §2.1 Coefficient valuations — `CoeffVal.lean` (L3)

### Plain-English proof substrate

[Q-Kob-def] and [Q-Gou-def] define the points `(i, ord_p a_i)` with `a_i = 0` "infinitely high"; the
coefficient valuation sequence is `i ↦ e (v (coeff i f))` in `WithTop ℝ`, `⊤` exactly at a vanishing
coefficient (`v x = ⊤ ↔ x = 0` on a field). A polynomial has finitely many points, hence is admissible
(L2.1). For a series, [Q-Kob-degen] excludes the case where "the vertical line through (0, 0) cannot be
rotated at all", which "has zero radius of convergence"; the honest version ([RM] §2.1.3) is: a line of
slope `m` lies on or below all the points exactly when the terms `‖aₖ‖ (b^m)^k` are bounded
(`b^{mk − e(v aₖ)} ≤ b^{−y}` ⟺ `y + mk ≤ e(v aₖ)`), boundedness at a radius implies restrictedness at
every smaller radius (`‖aₖ‖ cᵏ = ‖aₖ‖ c'ᵏ (c/c')ᵏ ≤ M (c/c')ᵏ → 0`), and restrictedness implies
boundedness ([RAG] `IsRestricted.hasGaussNorm`). So admissibility ⟺ bounded at some positive radius ⟺
restricted at some positive radius, and the vertical case is "`f ≠ 0`, restricted at no positive
radius" — [Q-Kob-degen]'s `Σ X^i/p^{i²}`.

### Leaves

- **L3.1–L3.2** `PowerSeries.coeffVal_eq_top_iff`, `_ne_top_iff` — Q: [Q-Gou-def] "if a_i = 0 … we just take
  it to be +∞"; [RM] §2.1.1 "Prove the value is ⊤ exactly at a vanishing coefficient". D: `coeffVal_apply`,
  L1.22. SURVIVED ([2] `f = 0` ✓).
- **L3.3** `coeffVal_eq_coe_iff` — M: `coeffVal v f i = ↑(e γ) ↔ v (coeff i f) = ↑γ`. D: L1.17 (←), and
  (→) `WithTop.ne_top_iff_exists` on `v (coeff i f)` + injectivity of `e` (`v.strictMono_embed.injective`,
  `WithTop.coe_inj`). SURVIVED.
- **L3.4** `finiteSupport_coeffVal` — D: `Set.ext`, `mem_finiteSupport`, L3.2. SURVIVED.
- **L3.5** `coeffVal_zero` — D: `funext`, `map_zero` of `coeff`, L1.1, L1.16. SURVIVED.
- **L3.6** `coeffVal_zero_of_coeff_zero_eq_one` — Q: [Q-Gou-def] "we may also assume that f(0) = 1" (then the
  first point is `(0, 0)`). D: `coeffVal_apply`, `h`, L1.23. SURVIVED.
- **L3.7** `exists_coeffVal_ne_top` — D: `PowerSeries.ext_iff` (`f ≠ 0 → ∃ i, coeff i f ≠ 0`), L3.2. SURVIVED.
- **L3.8–L3.10** `norm_coeff_mul_rpow_pow_{le,lt,eq}_one_iff` — Q: [Q-RM-2.1.2]. D: L1.25–L1.27 at
  `x := coeff k f`. SURVIVED.
- **L3.11** `hasGaussNorm_rpow_iff_exists_line` — Q: [RM] §2.3.2 "HasGaussNorm norm c f is equivalent to the
  supporting value being finite" (its line form); [Q-Kob-L5] "ord_p(a_i x^i) = ord_p a_i − ib'". M:
  `BddAbove (range (‖aₖ‖ (b^m)^k)) ↔ ∃ y, ∀ k, ↑(y + mk) ≤ coeffVal v f k`. D: (→) a bound `M`; if `M ≤ 0`
  every term is `0`, so `f = 0` (`norm_nonneg`, `pow_nonneg`, `mul_pos`) and any `y` works (L3.5, `le_top`);
  else `y := -logb b M` and `term ≤ M = b^{-y}` ⟺ `↑(y + mk) ≤ coeffVal` by L1.28-style reasoning
  (`norm_mul_rpow_pow_eq_rpow`, `Real.rpow_le_rpow_left_iff`, L1.15), with `aₖ = 0` giving `0 ≤ M`/`≤ ⊤`;
  (←) `M := b^{-y}` bounds every term the same way. A: [2] `f = 0` ✓ (both sides true); `m` negative ✓.
  [3] no hypothesis on `f`. [4] the roadmap's "supporting value finite" is L7.10's line form; this leaf is
  the Gauss-norm half of that equivalence. SURVIVED. (~50 LOC.)
- **L3.12** `isAdmissible_coeffVal_iff_exists_hasGaussNorm` — D: `isAdmissible_iff_exists_line`, L3.11, L1.15
  (a positive `c` is `b ^ logb b c`), `Real.rpow_pos_of_pos`. SURVIVED. (~15 LOC.)
- **L3.13** `isRestricted_of_hasGaussNorm` (`0 ≤ c < c'`) — Q: [Q-Kob-L5] "sufficiently far out, the
  (i, ord_p a_i) lie arbitrarily far above (i, b'i), in other words, ord_p(a_i x^i) → ∞"; [RM] §2.3.2
  "restrictedness is decay and is strictly stronger than boundedness. Prove the implication that holds".
  M: bounded at `c'` ⟹ restricted at `c < c'`. D: [RAG] `PowerSeries.isRestricted_iff'` (`Tendsto (‖aₖ‖ cᵏ)
  atTop (𝓝 0)`), `squeeze_zero` with the bound `M (c/c')^k` (`‖aₖ‖ cᵏ = ‖aₖ‖ c'ᵏ (c/c')ᵏ`, `div_pow`,
  `mul_div_cancel₀`-style with `c' > 0` from `hc.trans_lt hcc'`), `tendsto_pow_atTop_nhds_zero_of_lt_one`
  (`0 ≤ c/c' < 1`: `div_nonneg`, `div_lt_one`), `Filter.Tendsto.const_mul`, `mul_zero`. A: [2] `c = 0`:
  terms `0` for `k ≥ 1` ✓; `M ≤ 0`: `f = 0` ✓. [3] `c < c'` strict is needed ([RM]'s separating example
  `1 + pX + pX² + ⋯` at `c = c' = 1`, L12.22–23). SURVIVED. (~40 LOC.)
- **L3.14** `isAdmissible_coeffVal_iff_exists_isRestricted` — Q: [RM] §2.1.3 "the sequence of a power series
  is admissible exactly when f is restricted at some positive radius"; [Q-Kob-degen]. D: L3.12; (→) bounded
  at `c > 0` ⟹ restricted at `c/2` (L3.13, `half_pos`, `half_lt_self`); (←) restricted ⟹ bounded ([RAG]
  `IsRestricted.hasGaussNorm`). A: [1] the vertical example `Σ X^i/p^{i²}` ([Q-Kob-degen]): coefficient
  valuations `-i²`, not admissible (`not_isAdmissible_neg_sq`), and indeed not restricted at any radius
  (terms `p^{i²} cⁱ → ∞`) — consistent. [2] `f = 0`: admissible and restricted ✓. SURVIVED. (~20 LOC.)
- **L3.15** `IsRestricted.isAdmissible_coeffVal` — D: L3.14 (←). SURVIVED.
- **L3.16** `isVertical_coeffVal_iff` — Q: [Q-Kob-degen] "zero radius of convergence"; [RM] §0.2.3
  `IsVertical v := (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v`. D: unfold `IsVertical`, L3.7 + L3.2 (`f ≠ 0 ↔ ∃ i,
  coeffVal ≠ ⊤`), L3.14 negated (`not_exists`, `not_and`). SURVIVED. (~15 LOC.)
- **L3.17–L3.19** `Polynomial.coeffVal_eq_top_iff`, `_ne_top_iff`, `_eq_coe_iff` — as L3.1–L3.3 with
  `f.coeff i`. SURVIVED.
- **L3.20–L3.21** `finiteSupport_coeffVal`, `finiteSupport_coeffVal_finite` — Q: [RM] §2.1.1 "the sequence
  of a polynomial is finitely supported". D: `Set.ext`, `mem_finiteSupport`, L3.18, `Polynomial.mem_support_iff`,
  `Finset.mem_coe`; `Finset.finite_toSet`. SURVIVED.
- **L3.22** `coeffVal_coe` — Q: [RM] §2.2.5 "the coercion is compatible with everything in §2.1". D:
  `funext`, `Polynomial.coeff_coe`. SURVIVED.
- **L3.23** `isAdmissible_coeffVal` — Q: [RM] §2.1.3. D: L2.1, L3.21. SURVIVED.
- **L3.24** `hasGaussNorm_coe` — D: [RAG] `Polynomial.isRestricted_toPowerSeries c f` then
  `IsRestricted.hasGaussNorm`. A: [5] both [RAG] names elaborate (`names_pre.lean`). SURVIVED.

---

## §2.2 The polygon of a power series — `PowerSeries.lean` (L4)

### Plain-English proof substrate

[Q-Kob-ps]/[Q-Gou-ps]: the polygon of a series is the lower hull of its points, with the three endings;
in height form it is Layer 0's `newtonPolygon` of `coeffVal v f`, which satisfies the specification
exactly when the sequence is admissible (L3.14: restricted at some positive radius). [Q-Kob-vert]:
vertices are points of the sequence, so their heights are `e γ` ([RM] §2.2.3 "The height of the polygon
at a vertex lies in the image of e"), and a slope on a segment is "(m' − m)/(i' − i)" = `e(γ' − γ)/l`. For
`Γ = ℤ` with `e = Int.cast` the slope is `n/l`, a rational with denominator dividing the length. The
roadmap's "any polygon with finitely many segments is rational" fails for a terminal ray (plan D4), so
the statement is for bounded segments.
[Q-Kob-L5]/[Q-Gou-L748] (§2.2.4): if the series is restricted at every radius then for every `σ` some
line of slope `σ` lies below the points (L3.11), hence below the polygon, and the slopes are unbounded
(`slopesUnbounded_of_forall_line`); the unit slopes tend to `+∞` because, by convexity, slopes bounded by
`σ` on `[a, ∞)` would keep the polygon under the line `h a + σ(k − a)` while the points lie above a line
of slope `σ + 1`. Conversely a unit slope `> σ` at a finite index `j` puts all later points above a line
of slope `> σ` (the chord inequality), so `e(v aₖ) − σk → ∞`: restricted at `b^σ` — [Q-Kob-L5]'s "the
(i, ord_p a_i) lie arbitrarily far above (i, b'i)". The roadmap's sentence has the direction reversed
(plan D2).
§2.2.6–§2.2.8: `coeff (C c * f) = c · aₖ` adds `e(v c)` to every height ([Q-Gou-P340]); `coeff (rescale c f)
k = cᵏ aₖ` adds `k · e(v c)` ([Q-Kob-shear] "ord_p b_i = ord_p a_i − λi" with `c⁻¹`); `coeff (X^n f) k =
a_{k−n}` shifts right (L2.10); a compatible base change leaves the points unchanged; two normed additive
valuations scale the points by `scale` (L1.33) and the polygon with them (L2.24).

### Leaves

- **L4.1–L4.2** `isNewtonPolygonOf_newtonPolygon`, `_of_isRestricted` — Q: [RM] §2.2.1 "prove the
  specification holds: they satisfy IsNewtonPolygonOf under the hypotheses of §2.1.3"; [Q-Kob-ps]. D:
  [L0] `isNewtonPolygonOf_newtonPolygon` with `exists_isConvexMinorant_iff_isAdmissible`; L3.15. A: [2]
  `f = 0`: admissible, polygon `⊤` ✓. [3] admissibility cannot be dropped ([Q-Kob-degen]). SURVIVED.
- **L4.3–L4.4** `newtonPolygon_le`, `isConvexSeq_newtonPolygon` — D: L4.1 `.le_points`, `.convex`. SURVIVED.
- **L4.5** `newtonPolygon_zero` — D: L3.5, `newtonPolygon_eq_self isConvexSeq_top`. SURVIVED.
- **L4.6** `newtonPolygon_zero_eq` (`coeff 0 f ≠ 0`) — Q: [Q-Gou-def] "we plot the points (0,0)"; [RM] §0.2.5
  "The polygon passes through the first point". D: `IsNewtonPolygonOf.anchor_eq` with `i = 0` (vacuous
  `∀ k < 0`), L3.2. SURVIVED.
- **L4.7** `newtonPolygon_zero_of_coeff_zero_eq_one` — Q: [RM] §2.2.6 "if coeff 0 f = 1 the polygon is
  anchored at (0, 0)". D: L4.6 (`one_ne_zero`), L3.6. SURVIVED.
- **L4.8** `exists_eq_embed_of_isVertex` — Q: [Q-Kob-vert], [RM] §2.2.3 "The height of the polygon at a
  vertex lies in the image of e". D: `IsNewtonPolygonOf.eq_of_isVertex` (`h k = coeffVal v f k`), `hk.1`
  (`h k ≠ ⊤`) ⟹ `coeff k f ≠ 0` (L3.2) ⟹ L1.9 gives `γ`, L1.17. A: [2] the anchor is a vertex
  (`isVertex_anchor`) ✓. [4] exact. SURVIVED. (~12 LOC.)
- **L4.9** `exists_unitSlope_eq_div_of_isSegment` — Q: [Q-Kob-vert] "(m' − m)/(i' − i)"; [RM] §2.2.3 "Every
  unit slope … is (e γ) / l for some γ : Γ and some segment length l ≥ 1". D: L2.27 (with `hab.1`, `hab.2.1`
  vertices), L4.8 at `a` and `b` (`γ_a`, `γ_b`), `map_sub` of `e` (`γ := γ_b − γ_a`), `WithTop.untop₀_coe`,
  `Nat.cast_sub hab.2.2.1.le`. A: [1] the ray example (`⌈k√2⌉`, [L0] `newtonPolygon_ceil_sqrt_two`): its
  only vertex is `0`, no segment, the statement is silent — consistent with plan D4. SURVIVED. (~20 LOC.)
- **L4.10** `exists_int_unitSlope_eq_div_of_isSegment` — Q: [RM] §2.2.3 "for Γ = ℤ every slope is a rational
  number whose denominator divides the length of its segment". D: L4.9 with `w`, `he` (`w.embed n = n`),
  `Rat.cast_div`, `Rat.cast_intCast`, `Rat.cast_natCast`, `Nat.cast_sub`. A: [3] `he` is needed: an
  `ℤ`-valued bundle may embed by `n ↦ n · t`; the denominator claim is `Rat.den_dvd`-free (the rational
  `n/(b−a)` has denominator dividing `b − a` by construction). SURVIVED.
- **L4.11** `slopesUnbounded_newtonPolygon_of_forall_isRestricted` — Q: [RM] §2.2.4 "For a power series
  restricted at every positive radius ("entire"), prove SlopesUnbounded holds"; [Q-Gou-L748] "the slope of
  the polygon eventually becomes larger than b". D: L4.1 (admissible from `hf 1`), [L0]
  `IsNewtonPolygonOf.slopesUnbounded_of_forall_line` with, for each `σ`, the line from L3.11 (←) applied to
  `(hf (b^σ) (Real.rpow_pos_of_pos …)).hasGaussNorm`. A: [2] `f` a polynomial ✓; `f = 0` ✓ (trivially
  unbounded). [3] note Layer 0's `SlopesUnbounded` is trivially true when `coeff 0 f = 0` (a `⊤` unit
  slope before the anchor); the leaf is honest for `coeff 0 f ≠ 0`, which is where [L0]'s face lemmas use
  it (Layer 0 decision 5). SURVIVED. (~15 LOC.)
- **L4.12** `tendsto_unitSlope_newtonPolygon` — Q: [RM] §2.2.4 "the unit slopes tend to +∞"; [Q-Gou-L748].
  M: `Tendsto (unitSlope h) atTop (𝓝 ⊤)`, i.e. `∀ σ, ∀ᶠ j, ↑σ < unitSlope h j` (`WithTop.tendsto_nhds_top_iff`).
  D: given `σ`, a line `y + (σ+1) k ≤ coeffVal` (L3.11 at `b^{σ+1}`); if `h j ≠ ⊤` and `unitSlope h j ≤ σ`
  for some `j ≥ N`, convexity gives `h k ≤ h j + σ (k − j)` for `k ≥ j`?? — no: convexity bounds *below*,
  not above. Correct route: suppose for infinitely many `j` (finite) `unitSlope h j ≤ σ`; monotonicity of
  the unit slopes on the finiteness set then gives `unitSlope h i ≤ σ` for **all** finite `i`
  (`IsConvexSeq.monotoneOn`), so `h k ≤ h a + σ (k − a)` for all `k ≥ a` (`eq_add_sum_unitSlope`-style:
  `IsConvexSeq.le_add_nsmul_unitSlope_self`), contradicting `h k ≥ y + (σ+1) k` (`IsNewtonPolygonOf.line_le`)
  for large `k`. Hence eventually `σ < unitSlope h j` (either `⊤` or real `> σ`). A: [1] the attack "a
  convex sequence bounds heights from below only" was run against the first sketch and the route was
  corrected to use monotonicity of unit slopes; statement unchanged. [2] `f` a polynomial: eventually
  `unitSlope = ⊤` ✓; `f = 0` ✓; `coeff 0 f = 0` (anchor `a > 0`): unit slopes before `a` are `⊤`, the
  argument runs on `[a, ∞)` ✓. [5] `WithTop.tendsto_nhds_top_iff` elaborates (`Topology/Order/WithTop.lean`).
  SURVIVED. (~60 LOC.)
- **L4.13** `isRestricted_rpow_of_lt_unitSlope` (`h j ≠ ⊤`, `σ < unitSlope h j`) — Q: [Q-Kob-L5] "the
  (i, ord_p a_i) lie arbitrarily far above (i, b'i), in other words, ord_p(a_i x^i) → ∞, and f(X)
  converges" (`b' < b` ⟺ some unit slope exceeds `b'`); [SRC] `RadiusOfConvergence.isRestricted_of_lt_slope`.
  M: a unit slope `> σ` at a finite index ⟹ restricted at `b^σ`. D: case `unitSlope h j = ⊤`: then
  `h (j+1) = ⊤` (`unitSlope_eq_top_iff`, `hjf`), the finiteness set is an interval so `h k = ⊤` for all
  `k > j` (`IsConvexSeq.eq_top_of_le`), `h ≤ coeffVal` forces `coeff k f = 0` for `k > j` (`top_le_iff`,
  L3.1): `f` has finite support, [RAG] `isRestricted_of_finite_support`. Case real `τ := unitSlope h j > σ`:
  for `k ≥ j`, `h k ≥ h j + (k − j) τ` (`IsConvexSeq.add_nsmul_unitSlope_le`), so `coeffVal v f k ≥ h j +
  (k − j) τ`, and `‖aₖ‖ (b^σ)^k = b^{σk − e(v aₖ)} ≤ b^{σk − h j − (k − j)τ} = C · b^{−(τ − σ)k} → 0`
  (`Real.rpow_le_rpow_left_iff`, `tendsto_pow_atTop_nhds_zero_of_lt_one` on `b^{−(τ−σ)} < 1`, `squeeze_zero`,
  [RAG] `isRestricted_iff'`). A: [1] **the attack "`j` before the anchor" succeeded against the original
  statement** (`f = X^5 g` with `g` not restricted at `b^σ`: `h 0 = ⊤`, `unitSlope h 0 = ⊤ > σ`); the
  hypothesis `hjf : h j ≠ ⊤` was added to the skeleton (2026-10-06, before any ticket). [2] `f` a
  polynomial ✓ (first case). [3] `hf` needed for the polygon to exist. [4] [Kob84] states it for the sup
  `b`; the leaf is the pointwise version it proves. SURVIVED. (~70 LOC.)
- **L4.14** `unitSlope_le_of_not_isRestricted` — M: the contrapositive of L4.13. D: `not_lt.mp (fun h ↦ hσ
  (isRestricted_rpow_of_lt_unitSlope …))`. SURVIVED.
- **L4.15–L4.16** `coeffVal_C_mul`, `newtonPolygon_C_mul` — Q: [Q-Gou-P340] "the relation between the
  polygons of f(X) and of af(X)"; [RM] §2.2.6, §0.2.5 "newtonPolygon is unchanged by adding a constant to
  v" (translated by it). D: `PowerSeries.coeff_C_mul`, L1.3, L1.21, L1.17, `funext`; then [L0]
  `newtonPolygon_add_const (hf) (e γ)`. A: [2] `c = 1`: `γ = 0`, adds `0` ✓. [3] `c ≠ 0` encoded by
  `v c = ↑γ`. SURVIVED.
- **L4.17** `coeff_zero_C_inv_mul` — D: `coeff_C_mul`, `inv_mul_cancel₀ h0`. SURVIVED.
- **L4.18** `newtonPolygon_C_inv_mul` — Q: [RM] §2.2.6 "every series with coeff 0 f ≠ 0 becomes so after
  dividing by coeff 0 f, with the polygon translated by a constant". D: L4.16 with `c := (coeff 0 f)⁻¹`,
  `v c = ↑(−γ)` (L1.5, `LinearOrderedAddCommGroup.coe_neg`), `map_neg` of `e`. SURVIVED.
- **L4.19–L4.20** `coeffVal_rescale`, `newtonPolygon_rescale` — Q: [Q-Kob-shear] "ord_p b_i = ord_p(a_i/c^i) =
  ord_p a_i − λi" (with `c⁻¹` in place of `c`: `f(cX)` adds `λ i`); [RM] §2.2.7 "the polygon of f (cX) is
  sheared by e (v c)". D: `PowerSeries.coeff_rescale` (`cᵏ · aₖ`), L1.3, L1.4, `WithTop.coe_nsmul`,
  `map_nsmul` of `e`, `nsmul_eq_mul`, L1.21, L1.17; then [L0] `newtonPolygon_add_affine hf 0 (e γ)` and
  `zero_add`. A: [2] `c = 1` ✓; `k = 0` adds `0` ✓. [4] Koblitz divides by `c`, the roadmap substitutes
  `cX`; signs checked: `rescale c f = f (cX)` has `k`-th coefficient `cᵏ aₖ`, valuation `+ k e(v c)` ✓.
  SURVIVED. (~25 LOC.)
- **L4.21–L4.22** `coeffVal_X_pow_mul`, `newtonPolygon_X_pow_mul` — Q: [RM] §2.2.7 "the polygon of X^n · f is
  translated right by n". D: `PowerSeries.coeff_X_pow_mul'` (`if n ≤ d then coeff (d − n) f else 0`),
  `shiftRight` by `funext` + `split_ifs` (L3.5-style `⊤` for the zero coefficient: L1.1, L1.16); then L2.10.
  A: [2] `n = 0` ✓ (L2.5). SURVIVED.
- **L4.23–L4.24** `coeffVal_map`, `newtonPolygon_map` — Q: [RM] §2.2.7 "the polygon is unchanged under an
  isometric scalar extension L/K carrying a compatible normed additive valuation" (plan D7). D:
  `PowerSeries.coeff_map`, `hφ`, `he` (rewrite `embedTop`), `funext`; then `congrArg newtonPolygon`.
  A: [3] no admissibility needed (equality of the point sequences). [4] "isometric" is not used — the
  compatibility hypothesis carries it. SURVIVED.
- **L4.25–L4.27** `coeffVal_eq_scaleHeight`, `isAdmissible_coeffVal_iff`, `newtonPolygon_eq_scaleHeight` —
  Q: [Q-RM-2.2.8]. D: L1.33 pointwise (`funext`); L2.23 with `scale_pos`; L2.24 with `scale_pos`, L4.25.
  A: [2] `w = v`: `scale v v = 1` ✓ (`div_self`). [4] plan D9 for the direction of the scalar. SURVIVED.

---

## §2.2 The polygon of a polynomial — `Polynomial.lean` (L5)

### Plain-English proof substrate

[Q-Kob-def] for polynomials: the hull "joining (0, 0) with (n, ord_p a_n)" — in general the polygon is
anchored at the order of vanishing `natTrailingDegree f` and passes through `(natDegree f, e(v a_d))`,
is `⊤` outside `[natTrailingDegree f, natDegree f]`, and [Q-Gou-feat]: "the sum of all the lengths will
always be equal to the degree, and (0,0) and (n, v_p(a_n)) will always be vertices", i.e. there are
`natDegree f − natTrailingDegree f` unit slopes and both ends are vertices. The slope multiset is Layer
0's `slopeMultiset`. Rationality is L2.26–L2.27 specialised. `reverse f` has coefficients `a_{d−i}` on
`[0, d]` (`coeff_reverse`, `revAt_le`), so its polygon is the reflection (L2.17). `f.comp (C c * X)`
coerces to `rescale c ↑f` (both ring homs in `f` agreeing on `C a` and `X`), so the shear is L4.20.

### Leaves

- **L5.1** `newtonPolygon_coe` — Q: [RM] §2.2.5 "the polygon of a polynomial, viewed as a power series, is
  the polygon of the polynomial". D: unfold, L3.22. SURVIVED.
- **L5.2–L5.4** `isNewtonPolygonOf_newtonPolygon`, `newtonPolygon_le`, `isConvexSeq_newtonPolygon` — D: [L0]
  `isNewtonPolygonOf_newtonPolygon` via L3.23; projections. SURVIVED.
- **L5.5** `newtonPolygon_zero` — D: as L4.5 (`Polynomial.coeff_zero`). SURVIVED.
- **L5.6** `newtonPolygon_eq_top_of_lt_natTrailingDegree` — Q: [RM] §0.2.5 "is ⊤ before [the first point]";
  §2.2.2 "anchored at the order of vanishing at 0". D: `IsNewtonPolygonOf.eq_top_of_forall_eq_top` with
  `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree` (for `j ≤ k < natTrailingDegree`), L3.17. SURVIVED.
- **L5.7** `newtonPolygon_eq_top_of_natDegree_lt` — Q: [RM] §0.2.5 "is ⊤ beyond the last point". D:
  `IsNewtonPolygonOf.eq_top_of_forall_le` with `Polynomial.coeff_eq_zero_of_natDegree_lt`. SURVIVED.
- **L5.8** `newtonPolygon_ne_top` — D: `IsNewtonPolygonOf.ne_top_of_le_of_le` with `a := natTrailingDegree`
  (`Polynomial.trailingCoeff_eq_zero.not.mpr hf`, `trailingCoeff` unfolds to the coefficient), `b :=
  natDegree` (`Polynomial.coeff_natDegree`, `leadingCoeff_eq_zero.not.mpr hf`), L3.18. A: [2] `natDegree =
  natTrailingDegree` (a monomial): the single point ✓. SURVIVED.
- **L5.9** `newtonPolygon_eq_top_iff` — D: L5.6, L5.7, L5.8 (`not_or`, `not_lt`). SURVIVED.
- **L5.10** `newtonPolygon_natTrailingDegree` — D: `IsNewtonPolygonOf.anchor_eq` with the trailing degree
  (coefficients vanish below it, the trailing coefficient does not). SURVIVED.
- **L5.11** `newtonPolygon_natDegree` — Q: [Q-Gou-feat] "(n, v_p(a_n)) will always be vertices". D: L5.14
  then `IsNewtonPolygonOf.eq_of_isVertex`. SURVIVED.
- **L5.12** `anchor_newtonPolygon` — D: `IsNewtonPolygonOf.anchor_eq_sInf` (needs `∃ i, coeffVal ≠ ⊤`: the
  trailing coefficient), `finiteSupport_coeffVal` (L3.20), `Polynomial.natTrailingDegree_eq_support_min'`
  (or `le_antisymm` via `Nat.sInf_le`/`Nat.sInf_mem` and L5.6). A: [2] `f = C a`: anchor `0` ✓. SURVIVED.
  (~20 LOC.)
- **L5.13** `isVertex_natTrailingDegree` — D: `isVertex_anchor` + L5.12. SURVIVED.
- **L5.14** `isVertex_natDegree` — Q: [Q-Gou-feat]. D: `isVertex_of_succ_eq_top` (L5.4, L5.8 at `natDegree`,
  L5.7 at `natDegree + 1`). SURVIVED.
- **L5.15–L5.16** `slopeIndices_newtonPolygon`, `_finite` — Q: [Q-Gou-feat] "the sum of all the lengths will
  always be equal to the degree". D: `Set.ext`, `mem_slopeIndices_iff`, L5.9 twice (`Set.mem_Ico`,
  `Nat.lt_succ_iff`, `omega`); `Set.finite_Ico` (or `IsNewtonPolygonOf.slopeIndices_finite` with L3.21,
  which covers `f = 0`). A: [2] `f = 0`: `Ico 0 0 = ∅` — but L5.15 assumes `f ≠ 0`; L5.16 does not ✓.
  SURVIVED.
- **L5.17** `slopesUnbounded_newtonPolygon` — Q: [RM] §2.2.2 "SlopesUnbounded holds". D:
  `slopesUnbounded_of_finite` L5.16. SURVIVED.
- **L5.18** `newtonPolygon_zero_of_coeff_zero_eq_one` — D: L5.1-free: `IsNewtonPolygonOf.anchor_eq` at `0`,
  L3.19/L1.23 (`coeffVal 0 = 0`). SURVIVED.
- **L5.19** `card_newtonSlopes` — Q: [Q-Gou-feat]; [Q-Ked-def] "The total cardinality is at most n, with
  equality if and only if P_0 ≠ 0". M: `card = natDegree − natTrailingDegree` (for `f = 0` both are `0`).
  D: [L0] `card_slopeMultiset` (L5.16) = `(slopeIndices h).ncard`; for `f ≠ 0`, L5.15 and
  `Set.ncard_eq_toFinset_card'` + `Nat.card_Ico` (or `Set.ncard_Ico`); for `f = 0`, `slopeIndices = ∅`
  (L5.5, `unitSlope_eq_top_iff`), `Set.ncard_empty`, `Polynomial.natDegree_zero`,
  `natTrailingDegree_zero`. A: [2] `f = C a ≠ 0`: `0 = 0` ✓; `f = 0` ✓ handled. [4] Kedlaya pads with `+∞`
  when `P₀ = 0`; this roadmap counts `natDegree − natTrailingDegree` (convention 5: no padding). SURVIVED.
  (~25 LOC.)
- **L5.20** `count_newtonSlopes` — D: [L0] `count_slopeMultiset` L5.16. SURVIVED.
- **L5.21** `exists_isSegment_of_mem_slopeIndices` — D: L2.26 with L5.4, L5.16. SURVIVED.
- **L5.22** `exists_unitSlope_eq_div` — Q: [RM] §2.2.3. D: L5.21, L4.9 (through L5.1 or directly L2.27 +
  L4.8-style for polynomials), `l := b − a` (`Nat.sub_pos_of_lt`), `Nat.cast_sub`. SURVIVED.
- **L5.23** `exists_int_unitSlope_eq_div` — D: L5.21, L4.10 (via L5.1). SURVIVED.
- **L5.24** `coeffVal_reverse` — Q: [RM] §2.2.7 "the polygon of Polynomial.reverse f is the reflection
  i ↦ h (d − i) … where d = natDegree f". D: `funext`, `Polynomial.coeff_reverse`, cases `k ≤ d`:
  `Polynomial.revAt_le` (L2.11); `d < k`: `Polynomial.revAt_eq_self_of_lt`, `coeff_eq_zero_of_natDegree_lt`,
  L3.17, L2.12. A: [2] `f = 0`: `d = 0`, `reverse 0 = 0` ✓; `f = C a` ✓. SURVIVED. (~15 LOC.)
- **L5.25** `newtonPolygon_reverse` — Q: same; "⚠ … it is a milestone, not a remark". D: L5.24, L2.17 with
  `hv` from L3.17 + `coeff_eq_zero_of_natDegree_lt`. A: [1] `reverse` of `X^n f` loses the trailing zeros:
  `reverse (X · f) = reverse f` — consistent, since the reflection in `[0, d]` of a sequence anchored at
  `1` has its last point at `d − 1` and `⊤` at `d`… wait: `reflect d v d = v 0 = ⊤`, and `reverse (X f)` has
  degree `d − 1` with polygon `⊤` at `d` ✓ consistent. [2] `d = 0` ✓. SURVIVED. (~10 LOC.)
- **L5.26** `coe_comp_C_mul_X` — M: `↑(f.comp (C c * X)) = rescale c ↑f`. D: both sides are
  `Polynomial.coeToPowerSeries.ringHom` composed with `Polynomial.compRingHom (C c * X)` resp. `PowerSeries.rescale c`
  composed with the coercion; `Polynomial.ringHom_ext` on `C a` (`Polynomial.C_comp`, `Polynomial.coe_C`,
  `PowerSeries.rescale` of a constant by `PowerSeries.ext` + `coeff_rescale`, `coeff_C`) and on `X`
  (`Polynomial.X_comp`, `Polynomial.coe_mul`, `coe_C`, `coe_X`, `PowerSeries.rescale_X`). A: [2] `c = 0`:
  `f.comp 0 = C (f.eval 0)`, `rescale 0 f = C (constantCoeff f)` ✓ consistent. SURVIVED. (~25 LOC.)
- **L5.27** `newtonPolygon_comp_C_mul_X` — D: L5.1 (twice), L5.26, L4.20 with L3.23. SURVIVED.
- **L5.28–L5.30** `newtonPolygon_X_pow_mul`, `_C_mul`, `_C_inv_mul` — D: `Polynomial.coeff_X_pow_mul'`,
  `coeff_C_mul` + L2.10 / `newtonPolygon_add_const` with L3.23 (or L5.1 + L4.22/L4.16/L4.18 via
  `Polynomial.coe_mul`, `coe_pow`, `coe_X`, `coe_C`). SURVIVED.
- **L5.31** `newtonPolygon_map` — D: `Polynomial.coeff_map`, `hφ`, `he`, `funext`, `congrArg`. SURVIVED.
- **L5.32–L5.33** `newtonPolygon_eq_scaleHeight`, `newtonSlopes_eq_map` — D: L4.25-style (`funext`, L1.33),
  L2.24 with `scale_pos`, L3.23; L2.25 with L5.16. SURVIVED.

---

## Compatible extensions — `Extension.lean` (L6)

Substrate: Layer 1 §1.5.1–§1.5.2 (`normAddVal_algebraMap`: `normAddVal L (algebraMap K L x) = normAddVal K x`;
`normAddValQ_algebraMap`: the `ℚ`-valued one normalised at `algebraMap π` restricts, for `K` complete and
`L/K` algebraic) are exactly the compatibility hypotheses of L4.24; the embeddings are literally the same
maps (`AddMonoidHom.id ℝ`, `(Rat.castHom ℝ).toAddMonoidHom`).

- **L6.1–L6.2** `ofNormAddVal_algebraMap`, `ofNormAddVal_embed_eq` — Q: [RM] §1.5.1 "normAddVal L restricts to
  normAddVal K"; §2.2.7. D: [L1] `NormedField.normAddVal_algebraMap`; `rfl`. SURVIVED.
- **L6.3–L6.4** `ofNormAddValQ_algebraMap`, `ofNormAddValQ_embed_eq` — Q: [RM] §1.5.2 "normAddValQ L π restricts
  to normAddValQ K π". D: [L1] `NormedField.normAddValQ_algebraMap` (instance
  `NormedField.isCommensurable_algebraMap`); `rfl`. A: [3] `[CompleteSpace K] [Algebra.IsAlgebraic K L]` are
  Layer 1's hypotheses (its planning trap: an instance body that is `sorry` drops them — here they are
  explicit `variable`s and appear in the elaborated signatures ✓ `signatures.txt`). SURVIVED.
- **L6.5–L6.8** the four `newtonPolygon_ofNormAddVal(Q)_map` — D: L5.31 / L4.24 with L6.1–L6.4. A: [1]
  `ofNormAddValZ` is deliberately absent: `normAddValZ L (algebraMap x) = e · normAddValZ K x` ([L1]
  `normAddValZ_algebraMap`), so the polygon scales by the ramification index — recorded in the docstring.
  SURVIVED.
---

## §2.3 The supporting value — `SupportValue.lean` (L7)

### Plain-English proof substrate

[Q-Ked-vr]: *"v_r(Σ P_i T^i) = min_i {v(P_i) + ri} … is the y-intercept of the supporting line of the
Newton polygon of slope r"* — in this roadmap's orientation (points at `(i, v_i)`), the supporting line of
slope `m` has intercept `s(m) = inf_k (v_k − m k)`, an extended real: `⊥` when no line of slope `m` lies
below the points, `⊤` when there are no points. The points and their polygon have the same intercept: a
line below the points is a convex minorant, hence below the polygon ([L0] `line_le`), and the polygon is
below the points. On a convex sequence the infimum is attained wherever `m` separates the adjacent unit
slopes ([L0] `line_le_iff`), in particular at both endpoints of the face of slope `m` ([Q-Ked-C2]:
"the left and right endpoints of the segment of slope r … are the points where the support lines … touch
the polygon"; [L0] `faceRight_line_le`, `faceLeft_line_le`). Between two consecutive unit slopes `s_j ≤ m
≤ s_{j+1}` the line passes through `(j+1, h(j+1))`, so `s(m) = h(j+1) − m(j+1)` is affine in `m` — [RM]
§2.3.4 "piecewise affine with the unit slopes as its breakpoints". As an infimum of affine functions of
`m`, `s` is concave on the interval where it is finite. Finally [Q-Ked-def]: the polygon is "the
intersection of every closed halfplane lying above some nonvertical line containing all the points", i.e.
the supremum over `m` of its supporting lines `s(m) + m k` — the Legendre biconjugate, which recovers `h`
from `s` ([RM] §2.3.4 "the polygon and the Gauss norm function determine each other").

### Leaves

- **L7.1–L7.6** `toEReal_ne_bot`, `toEReal_le_toEReal`, `toEReal_lt_toEReal`, `toEReal_injective`,
  `toEReal_eq_top_iff`, `toEReal_of_ne_top` — M: `toEReal = WithBot.some` into `EReal = WithBot (WithTop ℝ)`.
  D: `WithBot.coe_ne_bot`, `WithBot.coe_le_coe`, `WithBot.coe_lt_coe`, `WithBot.coe_injective`,
  `WithBot.coe_inj` (with `(⊤ : EReal) = ↑(⊤ : WithTop ℝ)` by `rfl`, as `toEReal_top` is), `WithTop.coe_untop₀_of_ne_top`
  + `toEReal_coe`. A: [2] `x = ⊤` ✓ (`⊤ ≠ ⊥`). [5] `EReal`'s order is `WithBot`'s (`EReal` is a `def`, so
  `WithBot.*` lemmas apply after unfolding; the build of the two `rfl` lemmas confirms the defeq). SURVIVED.
- **L7.7–L7.8** `supportValue_le`, `le_supportValue_iff` — D: `iInf_le`, `le_iInf_iff` (`EReal` complete
  lattice). SURVIVED.
- **L7.9** `coe_le_supportValue_iff` — Q: [Q-Ked-vr] (intercept `y` of a line below all points). M: `↑y ≤ s
  ↔ ∀ k, ↑(y + mk) ≤ h k`. D: L7.8; per `k`: `h k = ⊤` gives `↑y ≤ ⊤ − ↑(mk) = ⊤` (`EReal.top_sub_coe`,
  `le_top`) and `_ ≤ ⊤`; `h k = ↑r` gives `(y : EReal) ≤ ↑(r − mk)` (`EReal.coe_sub`, `EReal.coe_le_coe_iff`)
  ↔ `y + mk ≤ r` (`le_sub_iff_add_le`) ↔ `↑(y + mk) ≤ ↑r` (`WithTop.coe_le_coe`). A: [2] `m = 0` ✓.
  SURVIVED. (~25 LOC.)
- **L7.10** `supportValue_ne_bot_iff` — Q: [RM] §2.3.2 "the supporting value being finite". D:
  `EReal.eq_bot_iff_forall_lt` negated (`s ≠ ⊥ ↔ ∃ y : ℝ, ↑y ≤ s`: from `¬ ∀ y, s < y`, `not_lt`), L7.9.
  SURVIVED. (~12 LOC.)
- **L7.11** `supportValue_eq_top_iff` — D: `iInf_eq_top`; `toEReal (h k) − ↑(mk) = ⊤ ↔ h k = ⊤` (`⊤` case
  `EReal.top_sub_coe`; finite case `EReal.coe_sub`, `EReal.coe_ne_top`). SURVIVED.
- **L7.12** `supportValue_mono` — D: `iInf_mono`, `EReal.sub_le_sub` (or `sub_le_sub_right`-style for
  `EReal`: `EReal.sub_le_sub (toEReal_le_toEReal.mpr (hgh k)) le_rfl`). A: [5] check the exact `EReal`
  subtraction-monotonicity name at execution (`EReal.sub_le_sub` elaborated? — not in `names_pre`; the
  worker verifies, with `EReal.add_le_add`/`EReal.neg_le_neg_iff` as the fallback since `x − y = x + (−y)`).
  SURVIVED (statement is clearly true: the map `t ↦ t − ↑(mk)` is monotone on `EReal`).
- **L7.13** `isAdmissible_iff_exists_supportValue_ne_bot` — D: `isAdmissible_iff_exists_line` ([L0]), L7.10.
  SURVIVED.
- **L7.14** `supportValue_newtonPolygon` — Q: [Q-Ked-vr] "the y-intercept of the supporting line of the
  Newton polygon" (the intercept is the same for the points and the hull); [RM] §2.3.1 "the supporting
  value is the infimum over k of h k − k·m". D: `le_antisymm`: `≤` by L7.12 (`newtonPolygon_le`); `≥`:
  cases on `supportValue v m`: `⊥` trivial; `⊤`: all `v k = ⊤` (L7.11) so `newtonPolygon v = ⊤`
  (`newtonPolygon_eq_self isConvexSeq_top` after `funext`), both `⊤`; `↑r`: `↑r ≤ s(v)` (L7.9) gives the
  line below the points, `IsNewtonPolygonOf.line_le` (spec from `hv`) gives it below the polygon, L7.9 back.
  A: [1] could a non-admissible `v` break it? excluded by `hv` (the polygon would be junk). [2] `v ≡ ⊤` ✓.
  SURVIVED. (~30 LOC.)
- **L7.15** `supportValue_eq_of_line_le` — Q: [Q-Ked-vr]. M: a line of slope `m` through `(n, h n)` below `h`
  ⟹ `s(m) = h n − mn`. D: `le_antisymm (supportValue_le h m n)` and `le_iInf`: for each `k`,
  `toEReal (h n) − ↑(mn) ≤ toEReal (h k) − ↑(mk)` from `hline k` (`EReal.coe_sub`, `EReal.coe_le_coe_iff`,
  `WithTop.coe_le_coe`, `WithTop.coe_untop₀_of_ne_top hn`; `h k = ⊤` gives `⊤`). A: [3] convexity of `h` is
  **not** needed (dropped from the skeleton 2026-10-06; the previous `IsConvexSeq.` prefix was an unused
  hypothesis). SURVIVED. (~25 LOC.)
- **L7.16** `IsConvexSeq.supportValue_eq_of_unitSlope` — Q: [L0] §0.5.1 "the affine function of slope σ
  through (n, h n) lies on or below h if and only if σ lies between the unit slopes adjacent to n". D:
  `IsConvexSeq.line_le_iff hh hn σ` (←) with `h₁`, `h₂`, then L7.15. SURVIVED.
- **L7.17** `IsConvexSeq.supportValue_eq_of_unitSlope_le_le` — Q: [RM] §2.3.4 "piecewise affine with the unit
  slopes as its breakpoints". M: `unitSlope h j ≤ m ≤ unitSlope h (j+1)` ⟹ `s(m) = h(j+1) − m(j+1)`. D:
  L7.16 at `n = j + 1`: `h₁'`: for `i < j + 1` finite, `unitSlope h i ≤ unitSlope h j ≤ m` by
  `IsConvexSeq.monotoneOn` (both `i`, `j` in the finiteness set: `h j ≠ ⊤` because `unitSlope h j ≤ ↑m < ⊤`
  forces `unitSlope h j ≠ ⊤`, `unitSlope_ne_top_iff`); `h₂'`: for `i ≥ j + 1` either `h i = ⊤` (then
  `unitSlope h i = ⊤ ≥ m`) or `unitSlope h (j+1) ≤ unitSlope h i` by monotonicity. A: [2] `j + 1` the last
  finite index: `unitSlope h (j+1) = ⊤ ≥ m` ✓ allowed by `h₂`'s `WithTop` form. [3] `hj` is needed to name
  the point. SURVIVED. (~35 LOC.)
- **L7.18–L7.19** `IsConvexSeq.supportValue_eq_faceRight`, `_faceLeft` — Q: [Q-Ked-C2]; [RM] §2.3.1 "the
  attained form 'the Gauss norm is the term at the right endpoint of the face of slope m'". D: [L0]
  `IsConvexSeq.faceRight_line_le hh h0 hu m` (the line of slope `m` through `(faceRight, h faceRight)` is
  below `h`) with `ne_top_faceRight h0 m`, then L7.15; same with `faceLeft_line_le`, `ne_top_faceLeft`.
  A: [3] `h0 : h 0 ≠ ⊤` and `hu : SlopesUnbounded h` are Layer 0's face hypotheses (decision 5); without `hu`
  the face may be infinite (a terminal ray) and `faceRight` junk. SURVIVED.
- **L7.20** `IsConvexSeq.supportValue_ne_bot` — D: L7.18 and `EReal.coe_ne_bot` after `toEReal_of_ne_top
  (ne_top_faceRight h0 m)`, `EReal.coe_sub`. SURVIVED.
- **L7.21** `IsNewtonPolygonOf.exists_eq_supportValue_iff` — Q: [RM] §2.3.3 "the Gauss norm is attained at an
  index exactly when the polygon has a vertex on the supporting line". M: some point on the supporting
  line ⟺ some vertex on it. D: `s := supportValue v m` is real (`≠ ⊥` by `hs`, `≠ ⊤` by L7.11 and `hv`);
  (←) a vertex `k` has `h k = v k` (`eq_of_isVertex`); (→) a point `k` on the line: the set `S := {j | toEReal
  (v j) − ↑(mj) = s}` is nonempty; take `j₀ := Nat.find`; `h j₀ = v j₀` because the line of slope `m` with
  intercept `s` is below the points (L7.9) hence below `h` (`line_le`), and `h j₀ ≤ v j₀` = the line's value
  at `j₀`; `j₀` is a vertex: `h j₀ ≠ ⊤`; if `j₀ = anchor h` done, else `h (j₀−1) ≠ ⊤` (interval) and `j₀ − 1
  ∉ S` gives `v (j₀−1) − m(j₀−1) > s`, while `h (j₀−1) ≥ s + m(j₀−1)`… the vertex condition `unitSlope h
  (j₀−1) < unitSlope h j₀`: `h j₀ − h (j₀−1) ≤ (s + m j₀) − (s + m(j₀−1))`? — careful: `h (j₀−1) ≥ line` gives
  `h j₀ − h (j₀−1) ≤ m`, and `h (j₀+1) ≥ line` gives `unitSlope h j₀ ≥ m`; strictness: if `unitSlope h (j₀−1)
  = m` then `h (j₀−1) = h j₀ − m` is on the line, and `v (j₀−1) ≥ h (j₀−1)` with `v (j₀−1)` strictly above
  the line only says `v (j₀−1) > h (j₀−1)` — no contradiction! **The naive "smallest index on the line is a
  vertex" is false** (the polygon may run along the line left of `j₀` through points strictly above it? no:
  if `h (j₀−1)` is on the line and `h` is convex with `h ≤ v`, then `h (j₀−1)` on the line below the point
  `v (j₀−1)` is fine; `j₀` need not be a vertex). Corrected route: the face. From the point `k` on the line
  and `h ≤ v`, the line is a supporting line touching `h` at `k`, so `m` lies between the unit slopes
  adjacent to `k` (`IsConvexSeq.line_le_iff` (→) applied to `h` at `n = k`, with `h k = v k`); hence the set
  `F := {j | h j − mj = s}` of polygon points on the line is a nonempty interval, and its left endpoint
  `j₁ := Nat.find` **is** a vertex: `unitSlope h (j₁−1) < m ≤ unitSlope h j₁` (if `j₁ − 1` were on the line
  with `h (j₁−1) ≠ ⊤` it would be in `F`; `unitSlope h (j₁−1) ≤ m` by `line_le_iff` at `j₁`, and equality
  would put `j₁ − 1` in `F`), or `j₁ = anchor h`. Then `toEReal (h j₁) − ↑(m j₁) = s` ✓. A: [1] the attack
  on the first sketch succeeded (described above); the leaf's statement is unchanged and the route now
  goes through `line_le_iff` and the left endpoint of the polygon's contact set. [2] `v` with all points on
  the line (an affine sequence): every index is on the line, the anchor is a vertex ✓. [3] `hv` was added
  to the skeleton (2026-10-06) after the attack "`v ≡ ⊤`: `s = ⊤`, every `k` satisfies `⊤ − ↑(mk) = ⊤` but no
  vertex exists" succeeded. SURVIVED. (~90 LOC.)
- **L7.22** `convex_setOf_supportValue_ne_bot` — Q: [Q-Ked-vr] "the function r ↦ v_r(P) is continuous" (its
  domain is an interval). M: `{m | s(m) ≠ ⊥}` is convex. D: `Convex ℝ` for a set of reals via
  `convex_iff_ordConnected` + `Set.OrdConnected`: for `m₁ ≤ m ≤ m₂` with lines `y₁ + m₁ k`, `y₂ + m₂ k`
  below the points (L7.10), the line `y₂ + m k ≤ y₂ + m₂ k ≤ h k` (as `k ≥ 0`, `m ≤ m₂`:
  `mul_le_mul_of_nonneg_right`) is below the points. A: [2] empty set ✓; all of `ℝ` ✓. SURVIVED. (~25 LOC.)
- **L7.23** `concaveOn_toReal_supportValue` — Q: [RM] §2.3.4 "m ↦ −log_b (gaussNorm norm (b ^ m) f) is
  concave"; [Q-Ked-vr] (an infimum of the affine functions `r ↦ v(P_i) + ri`). D: on `S := {m | s(m) ≠ ⊥}`
  (convex by L7.22): if `h ≡ ⊤` then `s ≡ ⊤`, `toReal ⊤ = 0`, `concaveOn_const`; otherwise `s(m)` is real on
  `S` and `(s m).toReal = ⨅ k : finiteSupport h, ((h k).untop₀ − m k)` (a real `ciInf`, bounded below on
  `S`; identify through L7.9: both are the greatest lower bound of the same set, `le_antisymm` via
  `le_ciInf`/`ciInf_le`), then `-(s m).toReal = ⨆ k, (m k − (h k).untop₀)` (`Real.iInf_neg`-style:
  `neg_iInf`/`ciSup_neg` — the worker uses `Real.sSup_neg`/`Real.iSup_neg` or proves the identity by
  `le_antisymm` directly) is convex on `S` by [L0]'s root lemma `convexOn_ciSup` (each `m ↦ m k − c_k` is
  affine, `ConvexOn.add`, `convexOn_const`, `LinearMap.convexOn`-style; bounded above on `S`), and
  `neg_convexOn_iff`/`ConcaveOn.neg` turns it into concavity of `s.toReal`. A: [1] is `s.toReal` concave
  on `S` when `S` has `s = ⊤`? excluded: `s = ⊤` only for `h ≡ ⊤` (L7.11), handled. [2] a single point
  `h = (c, ⊤, ⊤, …)`: `s(m) = c` constant ✓; a polynomial polygon: `S = ℝ` ✓. [3] no convexity of `h` needed
  (true for any sequence). SURVIVED. (~80 LOC.)
- **L7.24** `iSup_supportValue_add` — Q: [Q-Ked-def] "take the intersection of every closed halfplane lying
  above some nonvertical line containing all the points. The boundary of this region is called the Newton
  polygon" — the polygon is the supremum of its supporting lines. M: `⨆ m, (s(m) + mk) = toEReal (h k)` for
  `h = newtonPolygon v`, `v` admissible. D: `le_antisymm`: `≤`: `iSup_le`, for each `m`, `s(m) ≤ toEReal (v j)
  − mj` for all `j` (L7.7) and `s(m) ≤ s_h(m)` (L7.14) so `s(m) + mk ≤ toEReal (h k)` (L7.7 at `k` for `h`,
  `EReal.sub_add_cancel`-style for a real `mk`; `⊥ + _ = ⊥` fine). `≥`: three cases on `k`. (i) `h k ≠ ⊤`:
  pick a supporting slope `σ` at `k`: if `h (k+1) ≠ ⊤` take `σ := (unitSlope h k).untop₀` (then
  `line_le_iff` (←) holds: earlier finite unit slopes `≤ σ`, later `≥ σ`, by monotonicity), else if
  `k > anchor` take `σ := (unitSlope h (k−1)).untop₀`, else (single point) any `σ`; L7.16 gives `s_h(σ) =
  toEReal (h k) − σk`, so the term at `σ` equals `toEReal (h k)` and `le_iSup`. (ii) `h k = ⊤` with `k`
  beyond the last finite index `d` (`v` finitely supported case): for `m` large (`≥` the last unit slope),
  `s(m) = toEReal (h d) − md` (L7.16 at `d`), so `s(m) + mk = h d + m(k − d) → ⊤` as `m → ∞`; `iSup = ⊤`
  (`EReal.eq_top_iff_forall_lt`). (iii) `h k = ⊤` with `k < anchor`: for `m` very negative (`≤` the first
  unit slope), `s(m) = h a − ma`, `s(m) + mk = h a + m(k − a) → ⊤` as `m → −∞`. The case `h k = ⊤` with `v`
  infinitely supported and `k ≥ anchor` cannot occur (interval). A: [1] a non-admissible `v`: excluded by
  `hv` (the junk polygon would break (i)). [2] `v ≡ ⊤`: `s(m) = ⊤` for all `m`, `⊤ + mk = ⊤ = toEReal ⊤` ✓;
  `v` a single point ✓ (case (i) with any `σ`, cases (ii)/(iii) for the others). [3] convexity of the
  polygon is what makes (i) work (`line_le_iff` needs `IsConvexSeq`). SURVIVED. (~120 LOC; the largest
  leaf of the file — a worker may split off `exists_supporting_slope` for case (i) as a sub-ticket.)

Internal node (§2.3.4's "determine each other"): L7.24 recovers `h` from `s`; `s` is defined from `h`
(and equals the points' value by L7.14). SURVIVED.

---

## §2.3 The Gauss norm — `GaussNorm.lean` (L8)

### Plain-English proof substrate

Mathlib's `PowerSeries.gaussNorm norm c f = ⨆ k, ‖aₖ‖ cᵏ` (`gaussNorm_eq`) at the radius `c = b^m`, with
every term `‖aₖ‖ (b^m)^k = b^{mk − e(v aₖ)} = b^{−t_k}` where `t_k := e(v aₖ) − mk` (L1.24) and `b^{−t} = 0`
for the vanishing coefficients. The supremum of `b^{−t_k}` over `k` is `b^{−inf_k t_k}` because `t ↦ b^{−t}`
is a continuous order-reversing bijection — [Q-Ked-vr] read multiplicatively: `‖f‖_c = b^{−v_{−m}(f)}`,
and [Q-Gou-second] computed at a break: *"‖f(X)‖_c = p^{(m'−m)i} … the maximum is realized at the
degree k term"*, i.e. the Gauss norm is the term at the right endpoint of the face of slope `m'`
(L7.18). Boundedness of the terms is finiteness of the infimum (L3.11 ↔ L7.10). [Q-Gou-first] "i is the
largest integer such that ‖f(X)‖_c = |a_i|c^i" is attainment at a point on the supporting line (L7.21).
For polynomials, Mathlib's `Polynomial.gaussNorm` is a `Finset.sup'` over the support, always attained
(`exists_eq_gaussNorm`), and equals the power-series Gauss norm of the coercion
(`gaussNorm_coe_powerSeries`) once the norm is bundled as `NormedField.toAbsoluteValue K`.

### Leaves

- **L8.1** `Polynomial.gaussNorm_toAbsoluteValue` — Q: [RM] convention 11 "Polynomial.gaussNorm_coe_powerSeries
  is the bridge". D: `Polynomial.gaussNorm_coe_powerSeries (NormedField.toAbsoluteValue K) f hc` (needs
  `[ZeroHomClass] [NonnegHomClass]` — `AbsoluteValue.zeroHomClass`, `nonnegHomClass` ✓), and
  `⇑(NormedField.toAbsoluteValue K) = norm` (`rfl`, the definition's `toFun := norm`). A: [3] `0 ≤ c` is
  Mathlib's hypothesis. [5] names elaborate. SURVIVED.
- **L8.2** `Polynomial.exists_gaussNorm_coe_eq` — Q: [RM] §2.3.3 "for a polynomial it is always attained". D:
  `Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue K) c f`, L8.1. SURVIVED.
- **L8.3** `norm_coeff_mul_rpow_pow_eq_rpow` — D: L1.24 at `x := coeff k f`. SURVIVED.
- **L8.4** `hasGaussNorm_rpow_iff` — Q: [RM] §2.3.2 "Prove HasGaussNorm norm c f is equivalent to the
  supporting value being finite". D: L3.11, L7.10 (the two line forms are identical). SURVIVED.
- **L8.5** `hasGaussNorm_iff_supportValue_ne_bot` — D: L8.4 at `m := logb b c`, L1.15. SURVIVED.
- **L8.6** `gaussNorm_rpow_eq_of_supportValue_eq` — Q: [Q-Ked-vr] (multiplicative reading); [RM] §2.3.1
  "gaussNorm norm c f = b ^ (−(the supporting value of the polygon at slope m)) … equivalently the Gauss
  norm is the Legendre transform of the polygon". M: `s(m) = ↑r ⟹ ‖f‖_{b^m} = b^{−r}`. D: `gaussNorm_eq`;
  bounded (`HasGaussNorm` from L8.4, `EReal.coe_ne_bot`); `le_antisymm`: `ciSup_le`: each term `≤ b^{−r}`
  (`r ≤ t_k` from L7.7 + `EReal.coe_le_coe_iff`; `Real.rpow_le_rpow_left_iff`; zero terms by
  `Real.rpow_nonneg`); `≥`: for every `ε > 0` some `k` has `t_k < r + ε` (`exists_lt_of_ciInf_lt`-style on
  `EReal`: from `s = ↑r < ↑(r+ε)` and `iInf_lt_iff`), so the term `> b^{−(r+ε)}`, hence `⨆ ≥ b^{−(r+ε)}`
  (`le_ciSup`), and `b^{−r} = ⨆_ε b^{−(r+ε)}`: conclude by `le_of_forall_pos_lt_add`/continuity of `rpow`
  (`Real.continuousAt_const_rpow`-free: `le_of_forall_lt` with `Real.rpow_lt_rpow_left_iff` and the density
  of `b^{−(r+ε)}` below `b^{−r}`). A: [2] `f = 0`: excluded (`s = ⊤ ≠ ↑r`); `f` a monomial: `s(m) = e(v a) −
  mn`, Gauss norm `‖a‖ (b^m)^n` ✓ matches. [4] sign check [RM] §2.3.1: `1 − pX` over `ℚ_p`, `m = 2`:
  `t_0 = 0`, `t_1 = 1 − 2 = −1`, `s = −1`, Gauss norm `p^1 = p` ✓ (and the terms: `1`, `p^{−1} p^{2} = p` ✓).
  SURVIVED. (~70 LOC.)
- **L8.7** `gaussNorm_rpow_eq_rpow_neg_toReal` — D: `s ≠ ⊤` (L7.11 with L3.7), `EReal.coe_toReal hs' hs`, L8.6.
  SURVIVED.
- **L8.8** `supportValue_coeffVal_eq_neg_logb` — D: L8.7, `Real.logb_rpow` (`base_pos`, `one_lt_base.ne'`),
  `neg_neg`, `EReal.coe_toReal`. A: [2] `gaussNorm = 1`: `s = 0` ✓. SURVIVED.
- **L8.9** `supportValue_newtonPolygon_eq` — Q: [RM] §2.3.1 "the supporting value of the polygon". D: L7.14
  with `hf`. SURVIVED.
- **L8.10–L8.11** `gaussNorm_rpow_eq_norm_coeff_faceRight`, `_faceLeft` — Q: [Q-Gou-second] "the maximum is
  realized at the degree k term" (`k` the right endpoint of the face of slope `m'`); [RM] §2.3.1 "the
  attained form". D: L8.9, L7.18 (`isConvexSeq_newtonPolygon hf`, `h 0 ≠ ⊤` from L4.6 + L3.2, `hu`),
  `IsNewtonPolygonOf.eq_of_faceRight` (`h R = v R`, needs `v 0 ≠ ⊤` ✓ `h0`), so `s = ↑((v R).untop₀ − mR)`;
  L8.6 and L8.3 (`‖a_R‖ (b^m)^R = b^{mR − e γ_R}`) with `toEReal_of_ne_top`. A: [2] `m` below the first unit
  slope: `faceRight = 0`, Gauss norm `= ‖a₀‖` ✓ (`1 − X` at `m < 0`). [3] `hu` is needed (a terminal ray of
  slope `m` has `faceRight` junk). SURVIVED. (~30 LOC each.)
- **L8.12** `exists_gaussNorm_rpow_eq_iff` — Q: [RM] §2.3.3; [Q-Gou-first]. D: `s` real (L8.7's argument); a
  term equals the Gauss norm `b^{−r}` ⟺ `aₖ ≠ 0 ∧ t_k = r` (`Real.rpow_right_injective`-free:
  `Real.rpow_le_rpow_left_iff` both ways; `aₖ = 0` gives term `0 < b^{−r}`, `Real.rpow_pos_of_pos`) ⟺
  `toEReal (coeffVal k) − ↑(mk) = s`; then L7.21 with `hh := isNewtonPolygonOf_newtonPolygon` (admissible
  from L7.13/L8.4) and `hv` from L3.7. A: [2] `f` a polynomial: attained (L8.2) and indeed `faceRight` is a
  vertex on the line ✓ consistent with L8.10. SURVIVED. (~45 LOC.)
- **L8.13** `concaveOn_neg_logb_gaussNorm` — Q: [RM] §2.3.4 "is concave". D: `{m | HasGaussNorm (b^m)} = {m |
  s(m) ≠ ⊥}` (L8.4, `Set.ext`), `-logb b (gaussNorm (b^m) f) = (s m).toReal` on it (L8.8, `EReal.toReal_coe`),
  L7.23 with `ConcaveOn.congr`. SURVIVED. (~20 LOC.)
- **L8.14** `neg_logb_gaussNorm_eq_of_unitSlope_le_le` — Q: [RM] §2.3.4 "piecewise affine with the unit
  slopes as its breakpoints". D: L8.9, L7.17 (`isConvexSeq_newtonPolygon hf`, `hj`, `h₁`, `h₂`), so `s =
  ↑((h (j+1)).untop₀ − m(j+1))` (`toEReal_of_ne_top hj`, `EReal.coe_sub`); `f ≠ 0` from `hj` (else `h ≡ ⊤`);
  L8.8 and `EReal.coe_eq_coe_iff`. SURVIVED. (~20 LOC.)
- **L8.15** `toEReal_newtonPolygon_eq_iSup` — Q: [RM] §2.3.4 "the polygon and the Gauss norm function
  determine each other"; [Q-Ked-def]. D: `(iSup_supportValue_add hf k).symm` (L7.24). SURVIVED.
- **L8.16** `Polynomial.supportValue_coeffVal_ne_bot` — D: L8.4 (←) with L3.24 at `c := b^m`. SURVIVED.
- **L8.17** `Polynomial.gaussNorm_rpow_eq_norm_coeff_faceRight` — D: L5.1 (`newtonPolygon_coe`), L8.10 with
  L3.23 (through L3.22) and L5.17; `Polynomial.coeff_coe`. SURVIVED.

Internal nodes: §2.3.1's three forms (infimum L8.6, polygon L8.9, attained L8.10) are mutually
consistent by construction (each is derived from L8.6 + a Layer 0 face lemma); §2.3.2 (L8.4) and §2.3.3
(L8.12, L8.2) agree with the examples (`1 + pX + pX² + ⋯` at radius `1` is bounded but not restricted,
L12.22–23). SURVIVED.
---

## §2.4 Purity and first breaks — `Pure.lean` (L9)

### Plain-English proof substrate

[Q-Gou-D741]: "pure if its Newton polygon has only one slope"; in height form, Layer 0's `IsPure h m`
(every finite unit slope is `m`, and there is one). For a polynomial `h(X) = 1 + b₁X + ⋯ + bₙXⁿ`, Gouvêa's
remark and Problem 341: "pure of slope m … exactly when … for c = p^m, ‖f(X)‖_c = |b_n|c^n = 1, i.e., the
maximum occurs at the end and is equal to 1" — with a general constant term `a₀`: every term at `b^m` is at
most `‖a₀‖` (the points lie on or above the line of slope `m` through `(0, e(v a₀))`) and the leading term
equals it (the point `(d, e(v a_d))` is on the line). Conversely those bounds make the line the polygon:
it is a convex minorant through the first and last points, and any convex minorant lies below the chord
of its own values at `0` and `d` ([L0] `IsConvexSeq.le_chord`), hence below the line. For a genuine series
the leading-term clause becomes unboundedness at every larger radius: if the polygon is the ray of slope
`m` from `(0, e(v a₀))` and a line of slope `m' > m` lay below the points, the maximum of the ray and the
line would be a convex minorant above the ray at infinity — contradiction; conversely a unit slope `> m`
at `j` (the first) gives a line of slope `m' ∈ (m, unitSlope j)` through `(j, h j)` below the polygon, hence
bounded at `b^{m'}`. [Q-Gou-first] for the first break at `(l, ml)` (anchor `0`, general `a₀`): "v_p(a_j) ≥
mj for every j … v_p(a_i) = mi … v_p(a_j) > mj if j > i", i.e. Layer 0's `hasFirstBreak_iff` (the line
through the anchor below all points, equality at `l`, a strictly steeper line through `(l, v l)` below the
later points — which gives the strict inequality beyond `l`), and the Gauss-norm readings "|a_j|(p^m)^j ≤ 1
… = 1 … < 1" and "‖f(X)‖_c = 1".

### Leaves

- **L9.1** `IsPure.le_coeffVal` — Q: [RM] §2.4.1 "a pure polynomial of slope m has all its coefficients
  controlled by the line"; [Q-Gou-first] "there are no points below the line y = mx". D: `h 0 = v 0` (L4.6),
  pure ⟹ `h k = h 0 + k • m` for `k` in the finiteness set ([L0] `eq_add_nsmul_of_forall_unitSlope_eq`
  from the anchor `0`, with `hp.2` for the finite unit slopes), and `h k ≤ v k` (L4.3); for `h k = ⊤`,
  `v k = ⊤` too (`top_le_iff`). `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`. A: [2] `k = 0` ✓ (`m · 0`).
  [3] `h0` is needed (anchor `0`); `hf` for the polygon. SURVIVED. (~30 LOC.)
- **L9.2** `IsPure.norm_coeff_mul_rpow_pow_le` — Q: [Q-Gou-first] "|a_j|(p^m)^j ≤ 1". D: L1.28 at `j = 0`
  (`‖aₖ‖ cᵏ ≤ ‖a₀‖ c⁰`), `pow_zero`, `mul_one`, L9.1 (`↑(m(k − 0))`). SURVIVED.
- **L9.3** `IsPure.gaussNorm_rpow_eq` — Q: [Q-Gou-D741] "‖f(X)‖_c = … = 1" (with `a₀ = 1`). D: `gaussNorm_eq`,
  `le_antisymm (ciSup_le (L9.2))` and `le_ciSup (hbd) 0` with the term at `0` equal to `‖a₀‖`
  (`pow_zero`, `mul_one`), boundedness from L9.2 (`bddAbove_def`). SURVIVED. (~15 LOC.)
- **L9.4** `isPure_iff_of_infinite` — Q: [Q-Kob-ps] cases (2) and (3) (a single infinite segment),
  [Q-Gou-ex1] (`1 + pX + p²X² + ⋯`, "a line of slope one which contains infinitely many points"); [RM]
  §2.4.1 (plan D5). M: for infinitely many nonzero coefficients, pure of slope `m` ⟺ all terms at `b^m`
  are `≤ ‖a₀‖` and `f` is unbounded at every radius `> b^m`. D: (→) L9.2; and for `c > b^m` write `c = b^{m'}`
  (L1.15, `m' > m` by `Real.rpow_lt_rpow_left_iff`); if `HasGaussNorm (b^{m'})` then a line `y + m'k` lies
  below the points (L3.11) hence below `h` (`line_le`), but `h k = h 0 + mk` for all `k` (infinite support
  ⟹ `h k ≠ ⊤` for all `k`: the finiteness set is an interval containing `0`, unbounded since `v` has
  infinitely many finite values and `h k = ⊤ ⟹ v k = ⊤`), so `y + m'k ≤ h 0 + mk` for all `k`, i.e.
  `(m' − m)k ≤ h 0 − y`, false for large `k` (`exists_nat_gt`). (←) all points on or above the line `L k :=
  v 0 + mk`, so `L ≤ h` (`line_le`) and `h 0 = v 0`; the unit slopes are therefore `≥ m` (from `L ≤ h`
  and `h 0 = L 0`: `h (k+1) − h k ≥ …` via `IsConvexSeq.le_unitSlope_of_faceLeft_le`-free direct argument:
  if `unitSlope h j < m` for some finite `j`, by monotonicity all earlier unit slopes are `< m`, so `h j <
  h 0 + mj = L j ≤ h j`, contradiction); if some finite unit slope is `> m`, take the least such `j`
  (`Nat.find`): unit slopes `= m` before `j`, `≥ unitSlope h j` after, so for `m' ∈ (m, unitSlope h j)`
  (`exists_between`) the line of slope `m'` through `(j, h j)` is below `h` (`line_le_iff` (←)) hence
  below `v`, so `HasGaussNorm (b^{m'})` (L3.11) with `b^{m'} > b^m` — contradicting the second clause.
  Hence every finite unit slope is `m`, and one exists (infinite support): `IsPure`. A: [1] [Q-Gou-ex2]
  `1 + pX + pX² + ⋯` (pure of slope `0`): bounded at `1`, unbounded at every `c > 1` ✓ consistent. [2]
  `m` such that the first clause fails: not pure ✓. [3] `hinf` is necessary — for a polynomial the second
  clause is false (bounded at every radius) and L9.19 is the right statement; `h0` for the anchor.
  [4] [RM]'s "equality only at the two ends" replaced per plan D5. SURVIVED. (~110 LOC; a worker may split
  "unit slopes ≥ m from the line" as a sub-ticket.)
- **L9.5–L9.7** `HasFirstBreak.le_coeffVal`, `coeffVal_eq`, `lt_coeffVal` — Q: [Q-Gou-first] "First, … v_p(a_j)
  ≥ mj for every j. Second, … v_p(a_i) = mi. Third, … v_p(a_j) > mj if j > i". D: [L0]
  `IsNewtonPolygonOf.hasFirstBreak_iff` (with `hf`'s spec and `∃ i, v i ≠ ⊤` from `h0`) whose right-hand
  side has, with `anchor h = 0` (L5.12-style: `IsNewtonPolygonOf.anchor_eq_sInf` and `v 0 ≠ ⊤`, or
  `anchor_le`/`eq_top_of_lt_anchor`), the clauses `v 0 + k • m ≤ v k` (L9.5), `v l = v 0 + l • m` (L9.6), and
  `∃ m' > m, ∀ k ≥ l, v l + (k − l) • m' ≤ v k`; for `k > l` this gives `v k ≥ v l + (k−l) m' > v l + (k−l) m =
  v 0 + km` (L9.7; `WithTop.coe_lt_coe`, `mul_lt_mul_of_pos_left`, `Nat.cast_sub`). `WithTop.coe_nsmul`,
  `nsmul_eq_mul`. A: [2] `l = 1` ✓; `k = l + 1` ✓. [3] `h0` gives the anchor; `hf` the polygon. [4]
  Gouvêa's "subsequent points are really above the line" is exactly L9.7; the roadmap's "strictly between
  0 and the break index" is not claimed (plan D6; `1 + pX + p²X²` has its middle point on the line).
  SURVIVED. (~40 LOC together.)
- **L9.8** `HasFirstBreak.coeff_ne_zero` — D: L9.6 gives `coeffVal v f l ≠ ⊤` (`WithTop.add_ne_top`, L3.2 for
  `v 0`), L3.2. SURVIVED.
- **L9.9–L9.11** `HasFirstBreak.norm_coeff_mul_rpow_pow_{le,eq,lt}` — Q: [Q-Gou-first] "|a_j|(p^m)^j ≤ 1 …
  |a_i|(p^m)^i = 1 … |a_j|(p^m)^j < 1 if j > i" (with `‖a₀‖` for `1`). D: L1.28/L1.30/L1.29 at `j := 0`
  with L9.5/L9.6/L9.7 (`pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`). SURVIVED.
- **L9.12** `HasFirstBreak.gaussNorm_rpow_eq` — Q: [Q-Gou-first] "‖f(X)‖_c = 1". D: as L9.3 with L9.9.
  SURVIVED.
- **L9.13–L9.14** `isPure_coe_iff`, `hasFirstBreak_coe_iff` — D: unfold, L5.1. SURVIVED.
- **L9.15–L9.16** `Polynomial.IsPure.le_coeffVal`, `.norm_coeff_mul_rpow_pow_le` — D: L9.13, L9.1/L9.2 with
  L3.23 (via L3.22) and `Polynomial.coeff_coe`. SURVIVED.
- **L9.17** `IsPure.norm_coeff_natDegree_mul_rpow_pow_eq` — Q: [Q-Gou-D741] "|b_n|c^n = 1". D: `h d = v d`
  (L5.11, `f ≠ 0` from `h0`) and `h d = h 0 + d • m` (pure, all `d` unit slopes `m`, `eq_add_nsmul_of_forall_unitSlope_eq`),
  so `v d = v 0 + dm`; L1.30 at `j = 0`. SURVIVED. (~25 LOC.)
- **L9.18** `isPure_of_bounds` — Q: [Q-Gou-D741]/Problem 341 (⇐); [SRC] `FirstBreak.isPureSeries_of_bounds`.
  D: let `L := affineFrom 0 (v 0).untop₀ m` restricted to `[0, d]` (`⊤` beyond: `Set.Iic d |>.piecewise`);
  `L` is convex (`isConvexSeq_affineFrom`, `IsConvexSeq.piecewise_top` with `Set.ordConnected_Iic`); `L ≤
  coeffVal` by `hle` (L1.28 at `j = 0`) and `⊤` beyond `d` (L3.17, `coeff_eq_zero_of_natDegree_lt`); greatest:
  a convex minorant `g` has `g 0 ≤ v 0 = L 0`, `g d ≤ v d = L d` (`heq` via L1.30) and `IsConvexSeq.le_chord`
  on `[0, d]` gives `g k ≤ L k` (the chord of `L`'s endpoint values is `L`; `WithTop` nsmul arithmetic);
  beyond `d`, `L = ⊤`. So `IsNewtonPolygonOf (coeffVal v f) L`, `L = newtonPolygon v f`
  (`eq_newtonPolygon`), and `L`'s unit slopes are `m` on `[0, d)` (`unitSlope_affineFrom`), `⊤` from `d`:
  `IsPure` (`hd` for the existence clause). A: [2] `d = 1` ✓; interior points on the line (collinear) ✓
  allowed by `≤`. [3] `hd : 0 < natDegree` is needed for `IsPure`'s existence clause (a constant has no
  slope); `h0` for the anchor. SURVIVED. (~80 LOC.)
- **L9.19** `isPure_iff` — Q: [Q-Gou-D741] Problem 341 ("if and only if"). D: L9.16, L9.17 (→); L9.18 (←).
  SURVIVED.
- **L9.20** `isPure_iff_gaussNorm` — Q: [Q-Gou-D741] "‖f(X)‖_c = |b_n|c^n = 1". D: with `‖a₀‖ = 1` (`h0`,
  `norm_one`): (→) L9.3 (via L9.13, `gaussNorm = ‖a₀‖ = 1`) and L9.17; (←) `gaussNorm = 1` gives every
  term `≤ 1 = ‖a₀‖` (`PowerSeries.le_gaussNorm` with L3.24) and `‖a_d‖c^d = gaussNorm = 1 = ‖a₀‖`, then
  L9.18. SURVIVED. (~30 LOC.)
- **L9.21** `isPure_iff_hasFirstBreak` — Q: [Q-Gou-feat] "the sum of all the lengths will always be equal to
  the degree" (a single segment has length `d`). D: `HasFirstBreak h m d := 0 < d ∧ (∀ j < d, unitSlope h (0
  + j) = m) ∧ unitSlope h (0 + d) ≠ m` with `anchor = 0` (L5.12 and `h0`); `IsPure h m := (∃ j, unitSlope h j
  ≠ ⊤) ∧ ∀ j, unitSlope h j ≠ ⊤ → unitSlope h j = m`; the finite unit slopes are exactly `j ∈ [0, d)`
  (L5.15 with `f ≠ 0`), and `unitSlope h d = ⊤ ≠ ↑m` (`WithTop.top_ne_coe`). Both directions are this
  bookkeeping. SURVIVED. (~30 LOC.)

---

## §2.4.3 Distinguished series — `Distinguished.lean` (L10)

### Plain-English proof substrate

[Q-Gou-first]: "‖f(X)‖_c = 1, and i is the largest integer such that ‖f(X)‖_c = |a_i|c^i … i is the
distinguished number that appears in Proposition 7.2.3" — [Q-Gou-P723]'s hypothesis "‖f(X)‖ = |a_N|c^N and
‖f(X)‖ > |a_j|c^j for any j > N"; [Q-BGR-521] (2): "|g_s| = |g| and |g_s| > |g_ν| for all ν > s". The rigid
chain's `IsMulDistinguished c f s` has exactly these two clauses plus "(1) g_s is a unit", automatic over a
field. A first break at `(l, ml)` gives them at `c = b^m` by L9.12 and L9.10–L9.11. More generally, by L8.10
the Gauss norm at `b^m` is the term at `R = faceRight h m`, and by [L0] `faceRight_line_lt` every later
point lies strictly above the supporting line, so `R` is the largest attaining index; since the largest
attaining index is unique, `IsMulDistinguished (b^m) f i ↔ i = R`.

### Leaves

- **L10.1** `isMulDistinguished_iff` — Q: [Q-BGR-521] (1)–(2); [Mar16, Def. 1.24] as transcribed in the rigid
  chain's docstring. M: over a field the unit clause follows from the other two. D: `⟨fun h ↦ ⟨h.gaussNorm_eq,
  h.gaussTerm_lt⟩, fun ⟨h₁, h₂⟩ ↦ ⟨?, h₁, h₂⟩⟩` with the unit: `h₂ (i+1) (lt_add_one i)` gives `0 ≤ ‖a_{i+1}‖
  c^{i+1} < ‖a_i‖ c^i`, so `‖a_i‖ ≠ 0`, `a_i ≠ 0` (`norm_ne_zero_iff`), `isUnit_iff_ne_zero.mpr`, [RAG]
  `IsUnit.isNormMulUnit` (`NormMulClass K` ✓ for a normed field). A: [2] `f = 0`: both sides false (`0 < 0`)
  ✓. [5] [RAG] names `IsMulDistinguished.gaussNorm_eq`, `.gaussTerm_lt`, `.isNormMulUnit_coeff`,
  `IsUnit.isNormMulUnit` elaborate. SURVIVED. (~15 LOC.)
- **L10.2** `PowerSeries.HasFirstBreak.isMulDistinguished` — Q: [Q-Gou-first] (the distinguished number), [RM]
  §2.4.3 "its Gauss norm at c is attained at i and nowhere later"; [SRC] `FirstBreak.isMulDistinguished_of_hasFirstBreak`.
  D: L10.1 (←): `gaussNorm = ‖a₀‖ = ‖a_l‖ c^l` (L9.12, L9.10) and `‖a_t‖ c^t < ‖a₀‖ = ‖a_l‖ c^l` for `t > l`
  (L9.11, L9.10). A: [2] `l = natDegree` for a pure polynomial ✓ (L10.5). [4] [SRC] states it at
  `(normAddVal, id, exp 1)` with `‖a₀‖ = 1`; here general `(v, e, b)` and `a₀ ≠ 0`. SURVIVED. (~12 LOC.)
- **L10.3** `PowerSeries.isMulDistinguished_rpow_iff_faceRight_eq` — Q: [Q-Ked-C2] (the right endpoint is
  where the support line of slightly larger slope touches); [Q-Gou-second] "the maximum is realized at the
  degree k term" (`k` the right endpoint of the face). M: `IsMulDistinguished (b^m) f i ↔ faceRight h m = i`.
  D: (←) `R := faceRight h m`: `gaussNorm = ‖a_R‖ c^R` (L8.10), and for `t > R`, `h t > h R + m(t − R)`
  ([L0] `IsConvexSeq.faceRight_line_lt` with `isConvexSeq_newtonPolygon hf`, `h 0 ≠ ⊤`, `hu`), `v t ≥ h t`,
  `h R = v R` (`eq_of_faceRight`), so `e(v a_t) − mt > e(v a_R) − mR`, i.e. `‖a_t‖c^t < ‖a_R‖c^R` (L1.29) —
  the two clauses, unit by L10.1. (→) the largest attaining index is unique: if `i ≠ R`, say `i < R`, then
  `‖a_R‖c^R = gaussNorm = ‖a_i‖c^i > ‖a_R‖c^R` by `gaussTerm_lt R`, contradiction; if `R < i`, symmetric with
  the clause from (←). A: [1] a terminal ray of slope `m` (no `hu`): `faceRight` junk, and indeed the Gauss
  norm at `b^m` is attained only if some point lies on the ray — the hypothesis `hu` excludes the case ✓.
  [2] `i = 0` (`m` below the first slope): `faceRight = 0` and `‖a₀‖` dominates ✓. SURVIVED. (~50 LOC.)
- **L10.4** `Polynomial.HasFirstBreak.isMulDistinguished` — Q: [RM] §2.4.3 "a polynomial whose first break is at
  index i with slope m is distinguished at radius c = b ^ m of degree i". D: L9.14, L10.2 with L3.23 (via
  L3.22) and `Polynomial.coeff_coe`. SURVIVED.
- **L10.5** `Polynomial.IsPure.isMulDistinguished` — Q: [Q-Gou-D741] "the maximum occurs at the end". D: L9.21,
  L10.4. SURVIVED.
- **L10.6** `Polynomial.isMulDistinguished_rpow_iff_faceRight_eq` — D: L5.1, L10.3 with L3.23, L5.17. SURVIVED.

---

## `ℚ_p` with `v p = 1` — `Padic.lean` (L11)

- **L11.1** `normedAddValuation_apply` — Q: [RM] Acceptance "normAddValZ ℚ_[p] = Padic.addValuation". D: `rfl`
  to `normAddValZ ℚ_[p] x`, [L1] `NormedField.normAddValZ_padic_apply`. SURVIVED.
- **L11.2–L11.3** `normedAddValuation_embed`, `_embed_apply` — D: `rfl` (`Int.castAddHom ℝ`), `Int.coe_castAddHom`.
  SURVIVED.
- **L11.4** `normedAddValuation_base` — D: `ofNormAddValZ_base`, `Padic.norm_p` (`‖p‖ = p⁻¹`), `inv_inv`.
  SURVIVED.
- **L11.5** `normedAddValuation_natCast_prime` — Q: [RM] Examples "normAddValZ p = 1". D: L1.37 with
  `Padic.isUniformizer_p`. SURVIVED.
- **L11.6** `scale_normedAddValuation_ofNormAddVal` — Q: [Q-RM-2.2.8] "divided by log p". D: L1.38,
  `Padic.norm_p`, `Real.log_inv`, `neg_neg`. SURVIVED.

---

## Examples — `Examples.lean` (L12)

### Plain-English proof substrate

All over `ℚ_p` with `Padic.normedAddValuation p` (`v p = 1`, base `p`, embedding the cast), so a point's
height is `Padic.addValuation` of the coefficient. `1 − X`: points `(0,0), (1,0)`, pure of slope `0`;
`1 − pX`: points `(0,0), (1,1)`, slope `1` ([RM] Acceptance). `1 + pX + p³X²`: points `(0,0),(1,1),(2,3)`,
convex, so the polygon is the point sequence with unit slopes `1, 2`. `1 + pX + p²X²`: points
`(0,0),(1,1),(2,2)`, collinear: the middle point is on the polygon but not a vertex, slopes `1, 1` ([RM]
Examples "a polynomial with a collinear interior point"). `1 + 3^{2j+1}X²` over `ℚ_3`: points `(0,0)` and
`(2, 2j+1)`, pure of slope `(2j+1)/2 = j + ½` by L9.18 (the middle coefficient vanishes). `Φ_p = Σ_{i<p} X^i`
(`cyclotomic_prime`): all coefficients `1`, polygon flat at `0`; `Φ_p(X+1) · X = (X+1)^p − 1` so `Φ_p(X+1)`
has coefficients `C(p, i+1)`, and `Φ_p(X+1)/p` has constant term `1`, leading term `1/p` at `p − 1`, and
interior coefficients `C(p, i+1)/p` of norm `≤ 1` (`p ∣ C(p, i+1)` for `0 < i+1 < p`, `Nat.Prime.dvd_choose_self`);
with `c = p^{−1/(p−1)}` the terms are `≤ 1` and the leading term `p · p^{−1} = 1`: pure of slope `−1/(p−1)`
by L9.18 ([RM] Acceptance). [Q-Gou-ex1]: `Σ pⁱXⁱ` has points `(i, i)`, an affine sequence, its own polygon,
pure of slope `1`. `Σ p^{i²} Xⁱ`: points `(i, i²)`, [L0]'s parabola (`newtonPolygon_sq`, unit slopes
`2j + 1`), entire since `p^{−i²} cⁱ = (c/pⁱ)ⁱ ≤ (½)ⁱ` eventually. [Q-Gou-ex2]: `1 + pX + pX² + ⋯` has terms
`‖p‖ · 1 = p⁻¹` at radius `1`: bounded, not tending to `0`. And [Q-RM-2.2.8]'s `ℚ_p` instance is L5.32 with
L11.6.

### Leaves

- **L12.1** `isPure_one_sub_X` — Q: [RM] Acceptance "The polygon of 1 − X is the single unit segment of slope
  0". D: L9.18 with `m = 0` (`Real.rpow_zero`, `one_pow`, `mul_one`): coefficients by `Polynomial.coeff_sub`,
  `coeff_one`, `coeff_X` (`0`: `1`, `1`: `−1`, else `0`), `norm_one`, `norm_neg`, `norm_zero`,
  `Polynomial.natDegree` of `1 − X` is `1` (`Polynomial.natDegree_sub_eq_right_of_natDegree_lt`,
  `natDegree_X`, `natDegree_one`). A: [2] `p = 2` ✓ (no dependence on `p`). SURVIVED. (~30 LOC.)
- **L12.2** `newtonSlopes_one_sub_X` — D: [L0] `isPure_iff_slopeMultiset` (L5.16) with L12.1 and
  `card_newtonSlopes = 1` (L5.19: `natDegree 1`, `natTrailingDegree 0` via `Polynomial.natTrailingDegree_le_of_ne_zero`
  at `0` with `coeff 0 = 1`), `Multiset.replicate_one`. SURVIVED. (~15 LOC.)
- **L12.3–L12.4** `isPure_one_sub_p_mul_X`, `newtonSlopes_one_sub_p_mul_X` — Q: [RM] Acceptance "1 − pX has
  slope 1". D: as L12.1–L12.2 with `coeff 1 = −p`, `‖−p‖ · p¹ = 1` (`Padic.norm_p`, `inv_mul_cancel₀`),
  `Real.rpow_one`, L11.4. SURVIVED.
- **L12.5** `newtonSlopes_one_add_p_mul_X_add_p_cube_mul_X_sq` — Q: [RM] Examples "1 + pX + p³X² (slopes 1, 2)";
  Acceptance. D: the point sequence `w := (0, 1, 3, ⊤, ⊤, …)` (coefficients `1, p, p³`; heights via
  L11.1, `Padic.addValuation.apply`, `Padic.valuation_p`, `Padic.valuation_pow`) is convex
  (`isConvexSeq_iff_midpoint` or `IsConvexSeq` by hand: finiteness set `Iic 2`, unit slopes `1, 2, ⊤, …`
  monotone), so `newtonPolygon = w` (`newtonPolygon_eq_self`); `slopeMultiset w` computed from
  `slopeIndices w = {0, 1}` (`Set.Finite.toFinset`, `Multiset.map` over `{0,1}` of `untop₀ ∘ unitSlope`)
  `= {1, 2}` (`Multiset.insert_eq_cons`, `Multiset.map_cons`, `Multiset.map_singleton`). A: [2] the natural
  trap: `coeff 2 (1 + C p * X + C (p^3) * X^2) = p³` needs `Polynomial.coeff_add`, `coeff_C_mul_X_pow`,
  `coeff_C_mul`, `coeff_X` with `if` arithmetic — `simp` with `Polynomial.coeff_X_pow` etc. SURVIVED.
  (~70 LOC.)
- **L12.6–L12.8** the collinear `1 + pX + p²X²` — Q: [RM] Examples "a polynomial with a collinear interior
  point", Acceptance "its polygon has two points on it that are not vertices, and the slope multiset is
  nevertheless correct" (here one interior point, `1`). D: the point sequence `(0, 1, 2, ⊤, …)` is convex
  (affine on `[0, 2]`), so `newtonPolygon = coeffVal` (L12.6 at `1`); `IsVertex h 1 ↔ h 1 ≠ ⊤ ∧ (1 = anchor h ∨
  unitSlope h 0 < unitSlope h 1)`: `anchor h = 0` (L5.12), `unitSlope h 0 = 1 = unitSlope h 1`
  (`lt_irrefl`) — L12.7; `newtonSlopes = {1, 1}` as L12.5 (`Multiset.replicate 2 1` form) — L12.8. A: [2]
  consistent with L5.19 (`card = 2`) and L9.19 (pure of slope `1`). SURVIVED. (~60 LOC together.)
- **L12.9** `isPure_one_add_three_pow_mul_X_sq` — Q: [RM] Acceptance "1 + 3^{2j+1} X² over ℚ_3 is pure of slope
  j + ½, as an equality of rational numbers … This is the shape of statement the additive normalisation
  exists for". D: L9.18 at `m := j + 1/2` with `v := Padic.normedAddValuation 3` (`Nat.fact_prime_three`):
  `natDegree = 2` (`Polynomial.natDegree_add_eq_right_of_natDegree_lt`, `natDegree_C_mul_X_pow` with
  `3^{2j+1} ≠ 0`); coefficients `1`, `0`, `3^{2j+1}`; `‖3^{2j+1}‖ · (3^{j + 1/2})^2 = 3^{−(2j+1)} · 3^{2j+1} = 1`
  (`Padic.norm_p_pow`, `Real.rpow_natCast`, `← Real.rpow_mul`, `(j + 1/2) · 2 = 2j + 1` by `ring`,
  `Real.rpow_neg`, `inv_mul_cancel₀`); the middle term is `0 ≤ 1`. A: [2] `j = 0`: `1 + 3X²`, slope `½` ✓.
  [4] the slope is the real `j + 1/2`; its rationality is L5.23 (plan D10). SURVIVED. (~45 LOC.)
- **L12.10** `newtonSlopes_one_add_three_pow_mul_X_sq` — D: `isPure_iff_slopeMultiset` with L12.9 and
  `card = 2` (L5.19). SURVIVED.
- **L12.11–L12.12** `newtonPolygon_cyclotomic`, `isPure_cyclotomic` — Q: [RM] Acceptance "Φ_p itself has polygon
  flat at height 0". D: `Polynomial.cyclotomic_prime` (`Σ_{i<p} X^i`), `Polynomial.finset_sum_coeff`,
  `coeff_X_pow`, `Finset.sum_ite_eq` (coefficient `1` for `i < p`, `0` beyond), heights `0` (`Padic.valuation_one`
  / `AddValuation.map_one`), `⊤` beyond; the sequence `(0, …, 0, ⊤, …)` is convex (`isConvexSeq_affineFrom`-free:
  `IsConvexSeq.piecewise_top` of the zero sequence `isConvexSeq_zero_fun` on `Iio p`), so it is its own
  polygon (L12.11); unit slopes `0` on `[0, p − 1)`, `natDegree = p − 1 ≥ 1` (`Polynomial.natDegree_cyclotomic`,
  `Nat.totient_prime`, `Nat.Prime.one_lt`): `IsPure` (L12.12, directly or via L9.18 at `m = 0`). A: [2]
  `p = 2`: `Φ₂ = X + 1`, flat ✓. SURVIVED. (~60 LOC.)
- **L12.13** `coeff_cyclotomic_comp_X_add_one` — Q: [RM] Acceptance "Φ_p(X + 1) / p … Φ_p is the p-th
  cyclotomic polynomial". D: `Polynomial.cyclotomic_prime_mul_X_sub_one` composed with `X + 1`
  (`Polynomial.mul_comp`, `sub_comp`, `X_comp`, `one_comp`, `pow_comp`, `add_sub_cancel_right`): `Φ_p(X+1) · X
  = (X+1)^p − 1`; `Polynomial.coeff_mul_X` (`coeff (g * X) (i+1) = coeff g i`), `Polynomial.coeff_sub`,
  `coeff_X_add_one_pow`, `coeff_one` (`i + 1 ≠ 0`), `sub_zero`. A: [2] `i = 0`: `C(p,1) = p` ✓; `i ≥ p`: `0` ✓
  (`Nat.choose_eq_zero_of_lt`). SURVIVED. (~30 LOC.)
- **L12.14** `isPure_C_inv_mul_cyclotomic_comp_X_add_one` — Q: [RM] Acceptance "Φ_p(X + 1) / p is pure of slope
  −1/(p−1)". D: L9.18 at `m := −1/(p−1)`, `c := p^m`: coefficients `p⁻¹ · C(p, i+1)` (`Polynomial.coeff_C_mul`,
  L12.13); `coeff 0 = p⁻¹ · p = 1` (`Nat.choose_one_right`, `inv_mul_cancel₀`); `natDegree = p − 1`
  (`Polynomial.natDegree_C_mul` with `p⁻¹ ≠ 0`, `natDegree_comp`, `natDegree_cyclotomic`, `natDegree_X_add_C`);
  bounds: for `1 ≤ i ≤ p − 2`, `p ∣ C(p, i+1)` (`Nat.Prime.dvd_choose_self` with `i + 1 ≠ 0`, `i + 1 < p`), so
  `‖(C(p,i+1) : ℚ_p)‖ ≤ p⁻¹` (`Padic.norm_int_le_pow_iff_dvd` at `n = 1`, `zpow_neg_one`) and `‖coeff i‖ = p ·
  ‖C(p,i+1)‖ ≤ 1` (`norm_mul`, `norm_inv`, `Padic.norm_p`), while `c^i = p^{−i/(p−1)} ≤ 1`
  (`Real.rpow_le_one_of_one_le_of_nonpos`); at `i = p − 1`: `‖coeff‖ = p` and `c^{p−1} = p^{−1}`
  (`Real.rpow_natCast`, `← Real.rpow_mul`, `(−1/(p−1)) · (p−1) = −1` with `(p : ℝ) − 1 ≠ 0` from
  `Nat.Prime.one_lt`), product `1`; for `i ≥ p` the coefficient is `0`. A: [2] `p = 2`: `Φ₂(X+1)/2 = (X + 2)/2 =
  1 + X/2`, slope `−1`, `c = 2^{−1}`, leading term `2 · 2^{−1} = 1` ✓. [3] only divisibility of the
  interior binomials is needed, not their exact valuation. SURVIVED. (~120 LOC; the heaviest example.)
- **L12.15** `newtonPolygon_ofNormAddVal_eq_scaleHeight` — Q: [Q-RM-2.2.8] "In particular the polygon for
  normAddValZ on ℚ_p is the polygon for normAddVal divided by log p". D: L5.32 (`v := Padic.normedAddValuation
  p`, `w := ofNormAddVal ℚ_[p]`), L11.6. A: [4] direction per plan D9: `newtonPolygon (ofNormAddVal) =
  scaleHeight (log p) (newtonPolygon 𝓥)` ⟺ the normalised polygon is the unnormalised one divided by
  `log p` ✓. SURVIVED.
- **L12.16** `isPure_mk_p_pow` — Q: [Q-Gou-ex1]; [RM] Examples "1 + pX + p²X² + ⋯ (a pure series of slope 1)".
  D: `coeffVal = fun i ↦ (i : ℝ)` (`PowerSeries.coeff_mk`, `Padic.valuation_pow`, `valuation_p`, L11.1, cast
  arithmetic), an affine sequence (`isConvexSeq_affine 0 1`), its own polygon (`newtonPolygon_affine`),
  unit slopes `1` (`unitSlope_coe`), all finite: `IsPure`. A: [2] consistent with L9.4 (unbounded at every
  `c > p`). SURVIVED. (~30 LOC.)
- **L12.17** `isRestricted_mk_p_pow_sq` — Q: [RM] Examples "∑ pⁱ² Xⁱ, an entire series"; Acceptance. D: [RAG]
  `isRestricted_iff'`: terms `‖p^{i²}‖ cⁱ = p^{−i²} cⁱ = (c / pⁱ)ⁱ` (`Padic.norm_p_pow`, `zpow_neg`,
  `pow_mul`/`sq`); choose `N` with `2c ≤ p^N` (`pow_unbounded_of_one_lt`); for `i ≥ N`, `c/pⁱ ≤ 1/2`, term
  `≤ (1/2)ⁱ`; `squeeze_zero'` with `tendsto_pow_atTop_nhds_zero_of_lt_one` and `Filter.eventually_atTop`.
  A: [2] `c ≤ 1` ✓ (then `c/pⁱ < 1` already). SURVIVED. (~50 LOC.)
- **L12.18–L12.21** `coeffVal_mk_p_pow_sq`, `newtonPolygon_mk_p_pow_sq`, `unitSlope_newtonPolygon_mk_p_pow_sq`,
  `slopesUnbounded_newtonPolygon_mk_p_pow_sq` — Q: [RM] Examples "unit slopes 1, 3, 5, …". D: `coeff_mk`,
  L11.1, `Padic.addValuation.apply`, `Padic.valuation_pow`, `valuation_p`, `Int.cast_pow`/`Nat.cast_pow`
  (`((i^2 : ℤ) : ℝ) = (i : ℝ)^2`), `funext`; then [L0] `newtonPolygon_sq`, `unitSlope_newtonPolygon_sq`;
  `SlopesUnbounded` from the unit slopes `2j + 1` (`exists_nat_gt`) or from L4.11 with L12.17. SURVIVED.
- **L12.22** `hasGaussNorm_one_mk_ite` — Q: [Q-Gou-ex2]; [RM] §2.3.2 "give the example separating them". D:
  `HasGaussNorm` is `BddAbove (range …)`: every term is `‖1‖ · 1 = 1` or `‖p‖ · 1 = p⁻¹ ≤ 1`
  (`Padic.norm_p`, `inv_le_one_of_one_le₀`, `Nat.one_le_cast`), `bddAbove_def` with bound `1`. SURVIVED.
- **L12.23** `not_isRestricted_one_mk_ite` — Q: [Q-Gou-ex2] "if |x| = 1, then the series does not converge".
  D: [RAG] `isRestricted_iff'`; the terms are eventually the constant `p⁻¹` (`Filter.eventually_atTop`,
  `i ≥ 1`), so the limit would be `p⁻¹` (`Filter.Tendsto.congr'`, `tendsto_const_nhds`) and
  `tendsto_nhds_unique` gives `p⁻¹ = 0`, contradicting `inv_pos.mpr` (`Nat.cast_pos`). SURVIVED. (~20 LOC.)

Internal node (Examples vs theory): L12.2/L12.4/L12.10 use L5.19 and `isPure_iff_slopeMultiset` — if a
polynomial's `natTrailingDegree` were miscomputed the cardinalities would be off; all examples have
`coeff 0 ≠ 0`, so `natTrailingDegree = 0`. SURVIVED.

---

## Confidence gate (Step 5)

1. **Every leaf discharged**: by Mathlib (cited, elaborated in `scratch/names_pre.lean`), by [L0]/[L1]/[RAG]
   project declarations (sorry-free; cited by name, all elaborating), or by an earlier leaf of this tree.
   No API gap requiring a sub-development was found; the five largest leaves (L7.21, L7.23, L7.24, L9.4,
   L12.14) are each one declaration with a complete route and a size estimate.
2. **The Lean skeleton compiles**: `lake build PhD.TauCeti` → success, `sorry` warnings only; every signature
   elaborates (`scratch/signatures.txt`, 0 errors) — including the three statements repaired during the
   adversarial pass (L4.13/L4.14 `hjf`, L7.21 `hv`) and the unused hypothesis removed from L7.15.
3. **Every leaf has a verbatim quote** (a labelled passage above or an [RM] clause) and a Lean ↔ source match.
4. **Adversarial pass**: every leaf and internal node carries an attacks block; three attacks succeeded
   against *routes* (L2.16, L4.12, L7.21) and were repaired in the decomposition, two against *statements*
   (L4.13/L4.14 — a unit slope before the anchor; L7.21 — the zero sequence) and were repaired in the
   skeleton before any ticket; the roadmap's own text was found wrong in six places (plan D1, D2, D4, D5,
   D6, and the §2.4.4 completeness claim), each recorded with a counterexample.
5. **Prior-B2 log**: no name or shape match (see above).
6. **Mirrors the source**: the sections follow [RM] §2.1–§2.4 and the textbook passages they cite; every
   internal node names the quote(s) its children transcribe; LOC estimates cite the source passage's length
   where one exists (the Gouvêa first-segment analysis is a page; its leaves are ~10–40 LOC each) and are
   otherwise grounded in the Layer 0/1 proofs of the same shape.
7. **Single-conclusion**: every leaf has one conclusion; the `↔`-statements have the roadmap's own clauses
   as right-hand sides (L3.14, L8.4, L9.4, L9.19, L9.20, L10.1, L10.3 and their polynomial twins); the
   structure-field leaves L1.34/36/39 are definitions whose proof obligations are listed per field.

**Gate: PASS.** Deferred, not failed: [RM] §2.4.4 (plan D1), which needs Layer 3's factorisation and
completeness.
