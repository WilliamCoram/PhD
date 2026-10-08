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
