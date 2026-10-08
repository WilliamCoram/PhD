# Development Plan: Newton polygons, Layer 2 (the polygon of a polynomial and of a power series)

Board: `.mathlib-quality/tauceti-np-layer2/` (named; the default board path belongs to another
agent's Newton-polygon work, `tauceti-np-layer0/` and `tauceti-np-layer1/` are the completed
Layers 0 and 1). Specification: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 2
(introduction, §2.1–§2.4, Examples) and the Layer-2 lines of its Acceptance examples. Code:
`PhD/TauCeti/Code/NewtonPolygons/Coeff/`, module prefix `PhD.TauCeti.Code.NewtonPolygons.Coeff`,
never importing `PhD.Main.*` (CI-gated). The chain root `PhD/TauCeti.lean` imports the leaf
`Coeff/Examples.lean`. Planned 2026-10-06.

## Goal

The Newton polygon of a polynomial and of a power series over a nonarchimedean normed field `K`,
with respect to a **normed additive valuation** — the triple `(v, e, b)` of the roadmap's Layer 2
introduction, bundled as `NormedField.NormedAddValuation K Γ` — together with the dictionary to
Mathlib's Gauss norm, purity, first breaks and distinguishedness:

```lean
-- the valuation the polygon consumes (Layer 2 introduction; conventions 2 and 4)
structure NormedField.NormedAddValuation (K Γ) where
  toAddValuation : AddValuation K (WithTop Γ)
  embed : Γ →+ ℝ                       -- e, strictly monotone
  base : ℝ                             -- b > 1
  norm_eq_rpow' : v x = γ → ‖x‖ = base ^ (-embed γ)
def ofNormAddValZ K hπ : NormedAddValuation K ℤ      -- (normAddValZ K, Int.cast, ‖π‖⁻¹)
def ofNormAddValQ K π  : NormedAddValuation K ℚ      -- (normAddValQ K π, Rat.cast, ‖π‖⁻¹)
def ofNormAddVal K     : NormedAddValuation K ℝ      -- (normAddVal K, id, exp 1)

-- §2.1 the points, §2.2 the polygon
def PowerSeries.coeffVal v f : ℕ → WithTop ℝ := fun i ↦ WithTop.map e (v (coeff i f))
theorem PowerSeries.isAdmissible_coeffVal_iff_exists_isRestricted :
    IsAdmissible (coeffVal v f) ↔ ∃ c, 0 < c ∧ IsRestricted c f
def PowerSeries.newtonPolygon v f := NewtonPolygon.newtonPolygon (coeffVal v f)
def Polynomial.newtonPolygon v f;  def Polynomial.newtonSlopes v f : Multiset ℝ
theorem Polynomial.card_newtonSlopes : (newtonSlopes v f).card = natDegree f - natTrailingDegree f
theorem Polynomial.newtonPolygon_reverse : newtonPolygon v f.reverse = reflect (natDegree f) (newtonPolygon v f)
theorem PowerSeries.newtonPolygon_eq_scaleHeight : newtonPolygon w f = scaleHeight (log b / log b') (newtonPolygon v f)

-- §2.3 the Gauss norm as the supporting value (Legendre transform)
def NewtonPolygon.supportValue h m : EReal := ⨅ k, (h k - m k)
theorem PowerSeries.gaussNorm_rpow_eq_of_supportValue_eq : supportValue (coeffVal v f) m = s → gaussNorm norm (b ^ m) f = b ^ (-s)
theorem PowerSeries.hasGaussNorm_rpow_iff : HasGaussNorm norm (b ^ m) f ↔ supportValue (coeffVal v f) m ≠ ⊥
theorem PowerSeries.gaussNorm_rpow_eq_norm_coeff_faceRight : gaussNorm norm (b ^ m) f = ‖a_R‖ (b ^ m) ^ R,  R = faceRight h m

-- §2.4 purity, first breaks, distinguishedness
theorem Polynomial.isPure_iff : IsPure v f m ↔ (∀ k, ‖a_k‖ (b^m)^k ≤ ‖a₀‖) ∧ ‖a_d‖ (b^m)^d = ‖a₀‖
theorem PowerSeries.HasFirstBreak.lt_coeffVal : HasFirstBreak v f m l → l < k → e (v a₀) + m k < e (v a_k)
theorem Polynomial.HasFirstBreak.isMulDistinguished : HasFirstBreak v f m l → IsMulDistinguished (b ^ m) f l
```

and the roadmap's examples over `ℚ_p` with `v p = 1` (`Padic.normedAddValuation p`).

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 2 (introduction, §2.1–§2.4, Examples), conventions 1–2, 4–7, 10–11, Acceptance examples | the specification; every milestone is a numbered clause there |
| [Kob84] | N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58; text in `references/koblitz.txt` (symlink; PDF page `N` marked `===== PDFPAGE N =====`, book page = PDF page − 14); IV §3 pp. 97–98, IV §4 pp. 98–102 | definition of the polygon of a polynomial and of a power series, vertices, slopes and lengths; the three endings of a series' polygon; the degenerate (vertical) case; Lemma 5 (radius of convergence `p^b`, `b` the sup of the slopes); the remark `g(X) = f(X/c)` shears the polygon by the line `y = λx` |
| [Gou20] | F. Q. Gouvêa, *p-adic Numbers: An Introduction*, 3rd ed. (2020); text in `references/gouvea.txt` (symlink); §7.2 Proposition 7.2.3 (pp. 235–236), §7.4 pp. 251–269 | the rotating-line definition, "the sum of all the lengths will always be equal to the degree, and (0,0) and (n, v_p(a_n)) will always be vertices"; the first-segment analysis and its Gauss-norm reading (`‖f‖_c = 1`, "`i` is the largest integer such that `‖f(X)‖_c = |a_i| c^i`"); Definition 7.4.1 (pure), Problem 341 (pure ⟺ `‖f‖_{p^m} = |b_n| p^{mn} = 1`); the second-segment analysis (`‖f‖_c = p^{(m'-m)i}` attained at the degree-`k` term); Lemma 7.4.8 (radius `p^m`); the series examples `1 + pX + p²X² + ⋯`, `1 + pX + pX² + ⋯`; Problem 340 (dividing by `f(0)`) |
| [Ked07] | K. S. Kedlaya, *p-adic differential equations*, 18.787 (MIT, fall 2007), unit "Newton polygons", §§1–2; text in `references/kedlaya-newton-poly.txt` (extracted from the PDF at `https://kskedlaya.org/18.787/newton-poly.pdf`) | the polygon as "the intersection of every closed halfplane lying above some nonvertical line containing all the points", the slope multiset, and the **sloped valuation** `v_r(Σ P_i T^i) = min_i {v(P_i) + r i}`, "the `y`-intercept of the supporting line of the Newton polygon of slope `r`" — the supporting value of §2.3. ⚠ Kedlaya plots `(−i, v(P_i))`; in this roadmap's orientation his `v_r` is `supportValue h (-r)` |
| [BGR] | Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, 5.2.1/1 (quoted from the rigid-analytic-geometry board's `decomposition.md`) | "`|g_s| = |g|` and `|g_s| > |g_ν|` for all `ν > s`": distinguishedness as attainment-and-domination, the shape of `IsMulDistinguished` |
| [Mathlib] | `RingTheory/Polynomial/GaussNorm.lean`, `RingTheory/PowerSeries/GaussNorm.lean`, `RingTheory/MvPowerSeries/{GaussNorm,Restricted}.lean`, `Data/EReal/{Basic,Operations}.lean`, `Topology/Order/WithTop.lean`, `Algebra/Polynomial/{Reverse,Degree/TrailingDegree}.lean`, `RingTheory/PowerSeries/Basic.lean` (`rescale`), `RingTheory/Polynomial/Cyclotomic/Basic.lean`, `Analysis/Normed/Unbundled/RingSeminorm.lean` (`NormedField.toAbsoluteValue`), at pin `bbc4475e` | the Gauss norm vocabulary (convention 11), extended reals for the supporting value, the polynomial and series operations |
| [RAG] | `PhD/TauCeti/Code/RigidAnalyticGeometry/Restricted/PowerSeries/{Basic,GaussNorm,MulDistinguished}.lean` (Layer 0 of the rigid-analytic-geometry roadmap, complete 2026-10-02) | `PowerSeries.IsRestricted` (the `σ = Unit` case of Mathlib's multivariate predicate, with `isRestricted_iff` along `cofinite` and `isRestricted_iff'` along `atTop` — the shape [RM] describes), `IsRestricted.hasGaussNorm`, `Polynomial.isRestricted_toPowerSeries`, and `PowerSeries.IsMulDistinguished c f s` ([Mar16, Def. 1.24]) — see deviation D3 |
| [L0], [L1] | `PhD/TauCeti/Code/NewtonPolygons/{Basic,ConvexSeq,Slope,Face,Construction,Examples}.lean` and `AddVal/*.lean` (complete, sorry-free) | the polygon of a sequence and the additive valuations; cited by declaration name in every leaf |
| [SRC] | `PhD/Main/NewtonPolygons/{CoeffVal,FirstBreak,RadiusOfConvergence}.lean`, `PhD/Main/ForMathlib/NumberTheory/NewtonPolygon/PowerSeries.lean` (sorry-free at `fdc44e2`) | **read-only reference for proof ideas** (the term identities `‖a‖ exp(m)^k = exp(log‖a‖ + mk)`, admissibility from restrictedness, the first-break bounds, `isPureSeries_of_bounds`, `isMulDistinguished_of_hasFirstBreak`, `isRestricted_of_lt_slope` / `not_isRestricted_of_slopes_le`), instantiated there at `(normAddVal, id, exp 1)` on a segment-decorated polygon. Never imported; cited per leaf as "[SRC] File.decl" |

[RM] names Neukirch for Layer 1 only; for Layer 2 its sources are [Kob84] and [Ked07] (primary), [Gou20]
(elementary account and worked examples) and [BGR] (Gauss norm). Every leaf's quote below names which.

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---|---|---|
| Additive valuation on a normed field with a real embedding and a base | absent | DEFINE `NormedField.NormedAddValuation K Γ` (structure, `CoeFun`); three instances from [L1] |
| Newton polygon of a polynomial / series | absent (Mathlib has no Newton polygon) | DEFINE `Polynomial.newtonPolygon`, `PowerSeries.newtonPolygon`, `Polynomial.newtonSlopes` on top of [L0] |
| `PowerSeries.gaussNorm v c f` (`v : R → ℝ`, an `iSup`), `HasGaussNorm`, `gaussNorm_eq`, `le_gaussNorm`, `gaussNorm_nonneg` | present | USE; every Gauss-norm statement is phrased with `PowerSeries.gaussNorm norm c` |
| `Polynomial.gaussNorm v c p` (`v : F`, `[FunLike F R ℝ]`, a `Finset.sup'`), `gaussNorm_coe_powerSeries`, `exists_eq_gaussNorm`, `gaussNorm_mul` | present | USE through the single bridge `Polynomial.gaussNorm_toAbsoluteValue` with Mathlib's `NormedField.toAbsoluteValue K` (convention 11) |
| `PowerSeries.IsRestricted` | Mathlib's univariate file is **shadowed** in the Tau Ceti chain by [RAG] `Restricted/PowerSeries/Basic.lean` (the two cannot share an environment; the chain root imports both chains) | USE the [RAG] predicate, which is the roadmap's described shape (D3) |
| `IsMulDistinguished c f s` | [RAG] (not Mathlib) | USE (roadmap §2.4.3: "reuse the predicate of the adic-spaces roadmap's §0.5 material") |
| `EReal` (`WithBot (WithTop ℝ)`, complete linear order, `coe_sub`, `top_sub_coe`, `toReal`) | present | USE as the codomain of the supporting value; `NewtonPolygon.toEReal : WithTop ℝ → EReal` is `WithBot.some` |
| Topology on `WithTop ℝ`, `WithTop.tendsto_nhds_top_iff` | present (`Topology/Order/WithTop.lean`) | USE for "the unit slopes tend to `+∞`" |
| `Polynomial.reverse`, `coeff_reverse`, `revAt_le`, `reverse_natDegree`; `natTrailingDegree` API; `PowerSeries.rescale`, `coeff_rescale`, `rescale_X`; `coeff_X_pow_mul'`; `Polynomial.ringHom_ext` | present | USE for §2.2.7 |
| `Polynomial.cyclotomic_prime`, `coeff_X_add_one_pow`, `Nat.Prime.dvd_choose_self`-type divisibility (`Nat.Prime.dvd_choose_self` is absent at the pin — see T-EX ticket for the route via `Nat.Prime.emultiplicity_choose_prime_pow` / `Nat.Prime.dvd_choose_add`) | present | USE for the cyclotomic example |
| Supporting value / Legendre transform of a discrete convex function | absent | DEFINE `NewtonPolygon.supportValue` and prove the Legendre facts (§2.3) |
| Shifted / reflected / height-scaled sequence and its polygon | absent from [L0] | DEFINE `NewtonPolygon.shiftRight`, `reflect`, `scaleHeight` with spec transports (`Generic.lean`; Layer 0's home at upstreaming) |

## File structure and dependency graph

```text
Coeff/NormedAddValuation.lean  structure, three instances, element-level term dictionary (§2.1.2), scale (§2.2.8)   ← AddVal/Normed, Log.Base
Coeff/Generic.lean             shiftRight / reflect / scaleHeight transports, segments of a finite polygon           ← L0 Slope
Coeff/CoeffVal.lean            coefficient valuation sequences, admissibility ↔ restricted (§2.1.1, §2.1.3)          ← NormedAddValuation, L0 Basic, Polynomial.GaussNorm, [RAG] Restricted.PowerSeries.GaussNorm
Coeff/PowerSeries.lean         PowerSeries.newtonPolygon: spec, integrality, §2.2.4, §2.2.6–§2.2.8                 ← CoeffVal, Generic, L0 Face, Topology.Order.WithTop
Coeff/Polynomial.lean          Polynomial.newtonPolygon, anchoring, newtonSlopes, rationality, reverse, ops          ← PowerSeries
Coeff/Extension.lean           compatibility of ofNormAddVal / ofNormAddValQ along an extension, polygon invariance  ← Polynomial, AddVal/Extension
Coeff/SupportValue.lean        toEReal, supportValue, attainment, piecewise affine, concavity, biconjugate (§2.3)     ← L0 Face, EReal, Convex.Function
Coeff/GaussNorm.lean           Gauss norm = b^(-s), bounded ↔ s ≠ ⊥, attained forms, §2.3.3–§2.3.4                  ← Polynomial, SupportValue
Coeff/Pure.lean                IsPure, HasFirstBreak, Gauss-norm characterisations, line bounds (§2.4.1–§2.4.2)      ← GaussNorm
Coeff/Distinguished.lean       first break ⟹ IsMulDistinguished, distinguished degree = faceRight (§2.4.3)           ← Pure, [RAG] MulDistinguished
Coeff/Padic.lean               Padic.normedAddValuation p (v p = 1)                                                  ← NormedAddValuation, AddVal/Padic
Coeff/Examples.lean            the worked examples over ℚ_p                                                          ← Padic, Distinguished, Extension, L0 Examples, Cyclotomic  (chain-root leaf)
```

Tau Ceti homes are recorded in each module docstring (`TauCeti/NumberTheory/NewtonPolygon/*.lean`;
`Generic.lean` and `SupportValue.lean` belong to Layer 0's files at upstreaming).

## Generality and design decisions

1. **One bundle, `NormedAddValuation K Γ`.** The roadmap names the polygon `Polynomial.newtonPolygon v f`
   with the valuation explicit (convention 10) and describes the input as a valuation *equipped with*
   `e` and `b`; since `e` is data (for `Γ = ℝ` any positive multiple of `id` is an order embedding) it
   must travel with `v`, so the three are bundled and `v x` is the valuation through `CoeFun` (not
   `FunLike`: two bundles with the same valuation may differ in `e` and `b`). The structure and the
   whole layer are stated over `[NormedField K]` (no `IsUltrametricDist`, no nontriviality): the norm
   axiom forces ultrametricity (`NormedAddValuation.norm_add_le_max`), and only the three instances need
   Layer 1's `[NontriviallyNormedField K] [IsUltrametricDist K]`. A reviewer may prefer to split off the
   norm-free half (`v`, `e`) over a ring for §2.2's combinatorics; flagged, not done — the polygon of a
   polynomial over a ring needs `v x = ⊤ ↔ x = 0`, which already wants a field.
2. **The points are `WithTop.map e (v aᵢ)`** (`embedTop`), the polygon is Layer 0's `newtonPolygon` of
   them (convention 4); nothing is re-founded. Integrality and rationality are theorems
   (`exists_eq_embed_of_isVertex`, `exists_unitSlope_eq_div_of_isSegment`).
3. **Radii are powers of the base.** Every Gauss-norm statement takes the slope `m` and the radius
   `v.base ^ m` (`Real.rpow`); `rpow_logb` converts a positive radius to a slope.
4. **Gauss norms (convention 11).** Series statements use `PowerSeries.gaussNorm norm c f` with the bare
   `norm`; polynomial statements go through the coercion `(f : PowerSeries K)`, and
   `Polynomial.gaussNorm_toAbsoluteValue` (with Mathlib's `NormedField.toAbsoluteValue K`) is the only
   place Mathlib's `Polynomial.gaussNorm` appears. Recorded here as convention 11 asks.
5. **The supporting value is an `EReal`.** `supportValue h m = ⨅ k, (h k - m k)` in
   `EReal = WithBot (WithTop ℝ)`: `⊥` when unbounded below (the series is not bounded at radius `b ^ m`),
   `⊤` for the zero series, honest otherwise. `WithTop ℝ`'s `⨅` would be junk when unbounded, and
   convention 5's "`⊤` is the only junk value" is about polygons, not about this Legendre transform.
   Its real reading is `-log_b (gaussNorm norm (b ^ m) f)`.
6. **Generic transports by specification.** `newtonPolygon_shiftRight`, `newtonPolygon_reflect`,
   `newtonPolygon_scaleHeight` are proved through `IsNewtonPolygonOf` and uniqueness, never through the
   vertex walk (roadmap §0.2.4).
7. **Hypotheses.** Series statements carry `IsAdmissible (coeffVal v f)` (equivalently, restricted at
   some positive radius) wherever the polygon must exist; polynomial statements carry none. Statements
   about the anchor carry `coeff 0 f ≠ 0` (anchored at `0`), the setting of Layer 0's faces
   (its design decision 5); `coeff 0 f = 1` is the special case of §2.2.6.
8. **One conclusion per declaration.** Two-sided characterisations are single `↔`s whose right-hand
   sides are the roadmap's own clauses; no `∧`-chains except inside those.
9. **Namespaces.** `Polynomial.*`, `PowerSeries.*` for everything about `f`; `NormedField.NormedAddValuation`
   for the bundle; `NewtonPolygon` for the generic polygon material; `Padic.normedAddValuation`.

## Deviations from the roadmap text and errata found while planning (recorded, not silent)

- **D1 (§2.4.4, deferred).** "A polynomial that is irreducible over `K` and has `coeff 0 = 1` is pure" is
  **false without completeness**: over `ℚ` with the `p`-adic valuation, `1 + X + pX²` is irreducible
  (negative discriminant) and its polygon has slopes `0` and `1`. With `K` complete it is Gouvêa's
  Proposition 7.4.2, whose proof factors `f` at a break (Proposition 7.2.3 = the factorisation at the
  first break, roadmap §3.2). Layer 2 assumes no completeness ("introduced in Layer 3 where it is
  needed"), so **both halves of §2.4.4 are deferred to the Layer 3/4 boards**; nothing is stated here.
- **D2 (§2.2.4, direction).** "For a series restricted at some radius, prove the unit slopes are bounded
  above" is **backwards**: an entire series is restricted at every radius with unbounded slopes. The
  true statement (Koblitz Lemma 5, Gouvêa 7.4.8: radius of convergence `= b ^ (sup of the slopes)`) is
  that a unit slope **exceeding** `σ` forces restrictedness at `b ^ σ`, equivalently a series **not**
  restricted at `b ^ σ` has all unit slopes `≤ σ`. Stated as `isRestricted_rpow_of_lt_unitSlope` and
  `unitSlope_le_of_not_isRestricted`; the sharp bound is §4.4 as the roadmap says.
- **D3 (restrictedness and distinguishedness).** Mathlib's `Mathlib.RingTheory.PowerSeries.Restricted`
  (a `def` along `atTop`) is shadowed in this repository by the rigid-analytic-geometry chain's
  `Restricted/PowerSeries/Basic.lean` (`IsRestricted` as the `σ = Unit` case of
  `MvPowerSeries.IsRestricted`, with `isRestricted_iff` along `cofinite` and `isRestricted_iff'` along
  `atTop` — exactly the API the roadmap's "Existing Mathlib" section describes, i.e. the PR version).
  Because the chain root imports every leaf of both chains into one environment, Layer 2 **must** use the
  chain's copy; it does, and therefore also reuses `PowerSeries.IsMulDistinguished c f s` ([Mar16]) as
  roadmap §2.4.3 asks, rather than defining `IsDistinguishedAt`. The unit clause is automatic over a
  field (`isMulDistinguished_iff`). Layer 3 inherits this choice (its Weierstrass division comes from the
  same chain).
- **D4 (§2.2.3, rationality).** "Any polygon with finitely many segments is rational" is **false** for a
  terminal ray: the roadmap's own `v k = ⌈k√2⌉` has polygon the single ray of slope `√2` from the origin.
  Rationality is stated for unit slopes lying in a **bounded segment between two vertices**
  (`exists_unitSlope_eq_div_of_isSegment`, `exists_int_unitSlope_eq_div_of_isSegment`), which covers
  every unit slope of a polynomial (`Polynomial.exists_unitSlope_eq_div`).
- **D5 (§2.4.1, "equality only at the two ends").** Interior points may be collinear (`1 + pX + p²X²` is
  pure of slope `1` with its middle point on the polygon). Purity of a polynomial with `coeff 0 ≠ 0` is
  [Gou20, Problem 341]: every term at `b ^ m` is at most the constant term's **and** the leading term
  equals it (`Polynomial.isPure_iff`); for a genuine series the second clause becomes unboundedness at
  every larger radius (`PowerSeries.isPure_iff_of_infinite`).
- **D6 (§2.4.2, "strict inequality strictly between 0 and the break index").** False for the same
  reason (collinear interior points); Gouvêa's statement is strict inequality **beyond** the break
  (`HasFirstBreak.lt_coeffVal`), which is what the distinguishedness of §2.4.3 needs.
- **D7 (§2.2.7, scalar extension).** "Isometric scalar extension carrying a compatible normed additive
  valuation" is taken as data: a ring hom `φ : K →+* L` and `w : NormedAddValuation L Γ` with
  `w (φ x) = v x` and `w.embed = v.embed` (`newtonPolygon_map`); the concrete compatibilities are
  `ofNormAddVal` along any ultrametric normed `K`-algebra field and `ofNormAddValQ` along an algebraic
  extension of a complete field (Layer 1 §1.5). `ofNormAddValZ` is **not** compatible (ramification),
  as `Extension.lean`'s docstring records.
- **D8 (§2.2.7, `f (cX)`).** For polynomials `f (cX)` is `f.comp (C c * X)`; Mathlib has no coefficient
  lemma for it, so `coe_comp_C_mul_X` identifies it with `PowerSeries.rescale c ↑f` and the shear is read
  off the series statement.
- **D9 (§2.2.8, direction of the scalar).** With `‖x‖ = b ^ (-(e (v x))) = b' ^ (-(e' (v' x)))` the
  heights for `(v', e', b')` are `log b / log b'` times those for `(v, e, b)` (`scale`); on `ℚ_p` the
  polygon for `normAddVal` is `log p` times the polygon for `normAddValZ`, as the roadmap's example
  says.
- **D10 (Examples).** The acceptance claim "pure of slope `j + ½` as an equality of rational numbers" is
  stated as `IsPure (Padic.normedAddValuation 3) f ((j : ℝ) + 1/2)` and
  `newtonSlopes … = Multiset.replicate 2 ((j : ℝ) + 1/2)`; the polygon is real-valued (convention 4),
  and the rationality theorem `exists_int_unitSlope_eq_div` is the general statement.

## Skeleton status

`PhD/TauCeti/Code/NewtonPolygons/Coeff/*.lean`: 12 files, 256 open declarations (261 `sorry`s),
every proof `sorry`; 15 definitions/structures carry no `sorry` (`NormedAddValuation`, `embedTop`,
`scale`, `coeffVal` ×2, `newtonPolygon` ×2, `newtonSlopes`, `IsPure` ×2, `HasFirstBreak` ×2,
`shiftRight`, `reflect`, `scaleHeight`, `toEReal`, `supportValue`, `normedAddValuation`).
`lake build PhD.TauCeti` → `Build completed successfully (3654 jobs)`, `sorry` warnings only
(2026-10-06); the chain root imports `Coeff/Examples.lean`, which imports every Layer 2 module.
Elaborated signatures of every open declaration are in `scratch/signatures.txt` (0 errors;
`scratch/fullnames.py`); the current line of every open declaration is printed by
`scratch/sorries.py`.

## Name check

Every Mathlib / [L0] / [L1] / [RAG] name cited in the tickets' "Mathlib lemmas needed" blocks is
elaborated against the pin by `scratch/names_tickets_mathlib.lean` (generated from `tickets.md` by
`scratch/extract_names.py`): **492 names, 0 errors** (2026-10-06); planning-time spot checks are in
`scratch/names_pre.lean` (the names it found missing are not cited).

## Milestones

- **M1** = `PowerSeries.isAdmissible_coeffVal_iff_exists_isRestricted` (§2.1.3): the polygon of a
  series exists exactly when the series is restricted at some positive radius.
- **M2** = `Polynomial.newtonPolygon_reverse` (§2.2.7): the reflection, "a milestone, not a remark".
- **M3** = `PowerSeries.gaussNorm_rpow_eq_of_supportValue_eq` with `hasGaussNorm_rpow_iff` and
  `gaussNorm_rpow_eq_norm_coeff_faceRight` (§2.3.1–§2.3.2): the Gauss norm is the supporting value.
- **M4** = `Polynomial.HasFirstBreak.isMulDistinguished` (§2.4.3): first break ⟹ distinguished.
- **M5** = `Polynomial.isPure_one_add_three_pow_mul_X_sq` and
  `Polynomial.isPure_C_inv_mul_cyclotomic_comp_X_add_one` (Examples / Acceptance): `1 + 3^{2j+1} X²`
  pure of slope `j + ½`, `Φ_p(X+1)/p` pure of slope `-1/(p-1)`.

Each milestone ticket is preceded by a `CLEANUP-ALL` sweep (cadence rule), and the board ends with
`CLEANUP-FINAL`.

## Worker protocol

`/beastmode` inline as the main agent (user preference, 2026-09-05); one Lean process at a time on this
machine (other boards are running); after each ticket
`lake build PhD.TauCeti.Code.NewtonPolygons.Coeff.<File>` (the leaf `…Coeff.Examples` and the chain root
`PhD.TauCeti` before marking a milestone done) and `#print axioms` on each declaration (only `propext`,
`Classical.choice`, `Quot.sound`); `lake exe runLinter` on the module at every cleanup ticket; mark `done`
only with zero `sorry` in the ticket's declarations. [SRC] is read for proof ideas and ported to the
`(v, e, b)` form; it is never imported. The roadmap README's Layer 2 "Status" paragraph is written at
the end, recording D1–D10.
