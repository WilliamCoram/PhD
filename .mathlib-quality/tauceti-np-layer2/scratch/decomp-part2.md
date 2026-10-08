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
