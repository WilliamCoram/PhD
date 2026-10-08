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
