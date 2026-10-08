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
