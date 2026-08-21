# Decomposition: zeros of the characteristic power series are eigenvalues

## Skeleton location

All lemmas stated with `:= by sorry` in **`PhD/TateFredholm/Riesz.lean`** (single new
file; no existing file touched). `lake build PhD.TateFredholm.Riesz`: **✓ clean, 0
errors, sorries only** (2319 jobs) — verified 2026-08-04.

Sources on hand: Serre 1962 PDF (text-extracted pages 74–83 during planning; quotes
below are from that extraction, original French), Buzzard *Eigenvarieties* PDF
(extracted §3 pp. 20–24). Both saved under the session's tool-results; page numbers are
journal pages.

## Prior-B2 log consultation (Step 4.6)

`.mathlib-quality/b2_log.jsonl` (default board, read-only): 2 entries, both
`NewtonPolygon₀.*` (degenerate-polygon representability). **No match by name or shape**
with any leaf below. Clean.

## Plain-English proof (Step 1, transcribed from Serre §§5–7)

Let `E = c(I)`, `u` completely continuous (we use the repo's `IsCompactoid`, which is
what the determinant theory actually consumes), `H(t) = det(1 − tu) = Σ cₘ tᵐ`.

1. *(§6, p. 78)* The Fredholm resolvent `P(t,u) = H(t)/(1−tu) = Σ vₘ tᵐ` has
   `v₀ = 1`, `vₘ = cₘ·1 + u vₘ₋₁` ("On les calcule au moyen des formules de
   récurrence"), so each `vₘ` is a polynomial in `u`.
2. *(§6, Prop. 10 + Lemme 3, pp. 78–79)* `P` is entire: `|vₘ| ≤ r₁⋯rₘ` (decreasing
   rearrangement of the row norms), proved in three steps: **a)** finite dimension via
   Cramer — the resolvent matrix is the adjugate of `1 − tA`, whose entries' `tᵐ`
   coefficients are `±`-combinations of `m`-minors with pairwise-distinct rows;
   **b)** row-supported case by restriction; **c)** general case by truncation limit
   (`u(J) → u`, and the recursion gives `vₘ(J) → vₘ`).
3. *(§7, p. 80–81, Prop. 12's mechanism)* Apply the divided derivative `Δˢ` to
   `(1−tu)P(t,u) = H(t)` — since `1−tu` is affine in `t`, the product rule collapses to
   `(1−tu)ΔˢP − uΔ^{s−1}P = ΔˢH`; evaluate at `t = a` (all series entire) to get
   operators `Nₛ := (ΔˢP)(a,u)`, limits of polynomials in `u`, with
   `(1−au)N₀ = H(a)·1` and `(1−au)Nₛ = uNₛ₋₁ + (ΔˢH)(a)·1`.
4. *(§7, Prop. 11, p. 80)* `1−au` invertible ⟺ `H(a) ≠ 0`. (⟸) `H(a)⁻¹N₀` is a
   two-sided inverse by step 3 and commutation. (⟹) write `(1−au)⁻¹ = 1−v`; then
   `v = −au + auv` is completely continuous, and Cor. 1 to Prop. 7 *(§5, p. 76)* gives
   `det(1−au)·det(1−v) = det((1−au)(1−v)) = det 1 = 1`, so `det(1−au) = H(a) ≠ 0`
   (using `det(1−(a u)) = H_u(a)`, from `cₙ(au) = aⁿcₙ(u)`).
5. *(eigenvector extraction — the content of Prop. 12 for order `h ≥ 1`)* Let `a` be a
   zero of order `h ≥ 1`: `ΔˢH(a) = 0` for `s < h`, `ΔʰH(a)` a unit (Buzzard p. 22's
   ring-level definition). If `1−au` were injective, step 3 forces `N₀ = 0`, then
   inductively `Nₛ = 0` for `s < h`, and then `(1−au)N_h = ΔʰH(a)·1`, exhibiting an
   inverse (two-sided by commutation) — contradicting step 4(⟹) and `H(a) = 0`. So
   `ker(1−au) ≠ 0`.
6. *(field input; Buzzard p. 22, our Gauss-norm termination)* Over a complete
   nonarchimedean field, every zero of an entire `H` with `c₀ = 1` has finite order:
   `H(a) = 0` gives the factor `1 − a⁻¹X` by Weierstrass division at a radius
   `c > ‖a‖` (the linear factor is distinguished of degree 1 there; the remainder is
   the constant `H(a) = 0`); iterating, `‖H_s‖_c = ‖H‖_c (‖a‖/c)ˢ → 0` by Gauss-norm
   multiplicativity while `coeff 0 (H_s) = 1` forces `‖H_s‖_c ≥ 1` — so the iteration
   stops at some `h`, and the `Δ`-form of "order `h`" follows from the factorisation
   `H = (1−a⁻¹X)ʰ G`, `G(a) ≠ 0` by the divided-Taylor computation. Also `a ≠ 0`
   since `H(0) = c₀ = 1`.

Pointers: step 1 = p. 78 ("La résolvante de Fredholm … formules de récurrence");
step 2 = pp. 78–79 (Prop. 10, Lemme 3, steps a/b/c explicit on p. 79); step 3 =
pp. 80–81 ("En lui appliquant l'opérateur Δˢ"); step 4 = p. 80 (Prop. 11) + p. 76
(Cor. 1); step 5 = Prop. 12's data specialised to the kernel statement (we do NOT
transcribe the projector construction / `dim N(a) = h` — explicitly out of scope);
step 6 = Buzzard p. 22 ("One now checks by induction on h that H(T) = (1−a⁻¹T)ʰG(T)
… and then that G(a) is a unit") with our own termination argument replacing his
Noetherian-Banach-algebra context (attack A4-3 below records this deviation).

## Leaves

Legend: every leaf names its Lean declaration in `PhD/TateFredholm/Riesz.lean` (all
compile with `sorry`). Discharge verification was done against the Explore inventory of
2026-08-04 (exact signatures quoted there): `norm_minor_le_prod`,
`tendsto_minor_cofinite`, `norm_det_sub_det_le`, `charCoeff_eq_det_coeff`,
`exists_lim_of_cauchySeq`, `opNorm_mul_le`, `opNorm_sum_le`, `opNorm_pow_le`,
`norm_tsum_le_iSup`, `summable_of_tendsto_cofinite`, `tendsto_truncation_comp`,
`norm_eq_iSup_matrixCoeff`, `weierstrassDivision_exists_of_isMulDistinguished`,
`NormMulClass (Restricted R c)` instance, `Matrix.adjugate_apply`, `Matrix.mul_adjugate`,
`Matrix.det_mul`, `Matrix.det_smul`, `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
`Polynomial.hasseDeriv_coeff` (template only).

---

### Cluster A — divided derivatives and evaluation (`PowerSeries` namespace)

- **A1** (leaf, new def + 2 lemmas): `hasseDeriv`, `coeff_hasseDeriv`, `hasseDeriv_zero`
  - Source: [Buzzard2007, p. 22], verbatim:
    > "If f = Σ_{n≥0} aₙTⁿ is in A[[T]] and s ∈ ℤ_{≥0} then we define
    > Δˢf = Σ_{n≥0} (n+s choose s) a_{n+s} Tⁿ ∈ A[[T]]."
  - Lean ↔ source: `hasseDeriv k f := mk fun n => (n+k).choose k * coeff (n+k) f` is
    exactly the displayed formula. Mirrors `Polynomial.hasseDeriv_coeff` (verified in
    mathlib, `Mathlib/Algebra/Polynomial/HasseDeriv.lean:64`).
  - Discharge: `coeff_hasseDeriv` is `PowerSeries.coeff_mk`; `hasseDeriv_zero` is
    `ext` + `choose_zero_right`/`one_mul`.
  - Attacks: (1) counterexample: none — definitional; loogle for a clashing
    `PowerSeries.hasseDeriv` in mathlib: absent (only `Polynomial`/`LaurentSeries`).
    (2) edge cases: `k = 0` (⟹ `f`, lemma `hasseDeriv_zero`); `f = 0`; `n = 0` — all
    definitional. (3) drift: Buzzard's `(n+s choose s)` vs mathlib polynomial
    convention `(n+k).choose k` — equal (`Nat.choose_symm_diff` not even needed;
    same expression). Verdict: SURVIVED.
  - Prior-B2: no match.

- **A2** (leaf, new def + summability bridge): `evalT`, `summable_coeff_mul_pow`,
  `tendsto_norm_coeff_mul_pow_of_isRestricted`
  - Source: [Serre1962, §5 p. 76], verbatim:
    > "Le fait que det(1−tu) soit une fonction entière permet de substituer à t
    > n'importe quelle valeur dans K."
  - Lean ↔ source: substitution = `∑' n, coeff n f * a ^ n`; the hypothesis
    `Tendsto (‖coeff n f‖ * ‖a‖^n) atTop (𝓝 0)` is `isRestricted_iff'` at radius
    `‖a‖` (project `Restricted/Basic.lean:47`).
  - Discharge: `summable_of_tendsto_cofinite` (`Tate.lean:405`; needs
    `‖coeff n f * aⁿ‖ ≤ ‖coeff n f‖‖a‖ⁿ` = `norm_mul_le` + `norm_pow_le` chain);
    cofinite/atTop interchange `Nat.cofinite_eq_atTop`.
  - Attacks: (1) junk-value design (total def, hypotheses on lemmas) matches mathlib
    convention (`tsum` itself is junk-valued); no contradiction possible. (2) edge:
    `a = 0` — `0^0 = 1` gives `evalT 0 f = coeff 0 f`, which is the intended value;
    `f = C r` fine. (3) hypothesis strength: requiring restriction at exactly `‖a‖`
    (not `∀c`) is the weakest usable hypothesis — weaker (mere summability) would do
    for `evalT_add` but not for `evalT_mul`'s product; uniform shape chosen
    deliberately, recorded. Verdict: SURVIVED.
  - Prior-B2: no match.

- **A3** (leaf): `evalT_C`, `evalT_one`, `evalT_add`, `evalT_mul`
  - Source: standard (the source treats substitution as obvious); `evalT_mul` is the
    Cauchy product.
  - Discharge: `evalT_add` = `tsum_add` with summability from A2. `evalT_mul` =
    product-summability from the cofinite criterion — the `ε`-bad set of
    `(m,n) ↦ (coeff m f · aᵐ)(coeff n g · aⁿ)` is contained in
    `bad_f(ε/B_g) × bad_g(ε/B_f)` (finite × finite; bounds from
    `bddAbove_range_norm_of_tendsto_cofinite`, `Tate.lean:424`) — then
    `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
    (`Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:233`, takes product-summability
    as hypothesis; verified present) and `PowerSeries.coeff_mul` (antidiagonal).
  - Attacks: (1) the nonarchimedean-ring route
    (`tsum_mul_tsum_of_nonarchimedean`) needs a `NonarchimedeanRing R` instance from
    `IsUltrametricDist` whose existence we did NOT verify — the plan therefore routes
    through the generic `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` with the
    hand-proved product summability, which needs nothing beyond what `Tate.lean`
    exports. (2) edge: `f` or `g` with finitely many terms — degenerate but covered.
    (3) hypothesis test: norm-summability (`Summable ‖·‖`) would be FALSE in general
    ultrametric rings — the mathlib absolute-convergence Cauchy-product family is a
    trap; avoided by design. Verdict: SURVIVED (with the instance-risk explicitly
    routed around).
  - Prior-B2: no match.

- **A5** (leaf, 2 lemmas): `evalT_hasseDeriv_pow_mul_of_lt`,
  `evalT_hasseDeriv_pow_mul_self`
  - Source: [Buzzard2007, p. 22], verbatim:
    > "If f, g ∈ A[[T]] then it is possible to check that
    > Δˢ(fg) = Σ_{i=0}^{s} Δᶦ(f)Δ^{s−i}(g)."
    combined with the factorisation display "H(T) = (1 − a⁻¹T)ʰG(T)" (same page).
  - Lean ↔ source: our two lemmas are the evaluation at `a` of `Δˢ((1−bX)ʰ g)` with
    `b·a = 1`; only the `Δ`-of-affine-factor case of the product rule is needed:
    `Δˢ((1−bX)f) = (1−bX)Δˢf − bΔ^{s−1}f` (from `coeff` + Pascal), iterated `h`
    times. At `t = a` the factor `(1−ba) = 0` kills all terms except the fully
    differentiated one.
  - Discharge: coefficient computation with `Nat.choose` Pascal
    (`Nat.succ_sub_one`, `Nat.choose_succ_succ`), `evalT_mul`/`evalT_add` (A3),
    induction on `h`. Grounding: Buzzard proves the analogous claim in 4 lines
    (p. 22); expect ~60–90 LOC.
  - Attacks: (1) tried `s = 0, h = 1`: `evalT a ((1−bX)g) = (1−ba)·… = 0` ✓ matches.
    (2) tried `h = 0`: `_self` says `evalT a g = evalT a g` ✓ degenerate OK;
    `_of_lt` has no `s < 0` — vacuous ✓. (3) over a RING with `b·a = 1` but `a·b ≠ 1`?
    `R` is commutative here (`NormedCommRing`) — no chirality trap. (4) drift: Buzzard
    states these over Noetherian Banach `A`; our `R` is a Banach–Tate commutative
    ring — his proof (formal coefficient algebra) never uses Noetherian; checked
    line-by-line on p. 22. Verdict: SURVIVED.
  - Prior-B2: no match.

- **A4** (leaves, field): `exists_factor_of_evalT_eq_zero`,
  `exists_order_of_evalT_eq_zero`
  - Source: [Buzzard2007, p. 22], verbatim:
    > "If h ≥ 1 and H = 1 + a₁T + … then this implies that −1 = a(a₁ + a₂a + …) and
    > hence that a is a unit. One now checks by induction on h that
    > H(T) = (1 − a⁻¹T)ʰ G(T), where G ∈ A{{T}}, and then that G(a) is a unit."
  - Lean ↔ source: `exists_factor` is one induction step (peel one linear factor);
    `exists_order` is the full statement, producing Buzzard's `Δ`-form order. The
    `a ≠ 0` conjunct is the quoted "a is a unit" specialised to a field, proved from
    `evalT 0 f = coeff 0 f = 1 ≠ 0`.
  - Discharge (factor step): the linear factor `ℓ = 1 − a⁻¹X` at radius `c > ‖a‖`
    has Gauss-dominant top coefficient (`‖a⁻¹‖c > 1`), so `IsMulDistinguished c ℓ 1`
    (fields have `NormMulClass K`);
    `weierstrassDivision_exists_of_isMulDistinguished`
    (`ForMathlib …/MulWeierstrassDivision.lean:343`, `[CompleteSpace K]` ✓) gives
    `f = ℓ·q + r` with `deg r < 1`; evaluating at `a` (A3, `evalT` of the
    `Restricted` representatives' underlying series) gives `r = C (f(a)) = 0`.
    Discharge (termination): `NormMulClass (Restricted K c)` instance
    (`ForMathlib …/MvPowerSeries/Restricted/GaussNorm.lean:269`) gives
    `‖f‖ = ‖ℓ‖·‖q‖` with `‖ℓ‖ = c/‖a‖ > 1`; `coeff 0` of each successive quotient
    is `1` (from `ℓ`'s constant term `1`), and `1 = ‖coeff 0‖·c⁰ ≤ ‖·‖`
    (`le_gaussNorm`) bounds below — geometric shrinking terminates. The `Δ`-form
    conversion is A5.
  - Attacks: (1) counterexample hunt: an entire series with a zero of infinite order
    would refute termination — over a FIELD impossible by exactly the Gauss-norm
    argument; over a general Tate ring the statement is FALSE-ish (zero divisors),
    which is why A4 alone is field-scoped — scope verified against the skeleton
    (section `Order` has the field variables). (2) edge: `a` with `‖a‖ = 0` ⟹
    `a = 0` (field norm faithful) — excluded by the `a ≠ 0` conjunct proved first;
    radius choice `c := ‖a‖ + 1` always valid. (3) seam attack (project memory:
    restricted-seam-convention): statements are phrased on RAW `PowerSeries` with
    `IsRestricted` hypotheses; the `Restricted` subtype appears only inside proofs —
    term-mode seam crossings (`Subtype.ext`-style), never `rw` across the seam.
    (4) discharge attack: verified `weierstrassDivision_exists…` signature takes
    `g : Restricted A c`, `hg : IsMulDistinguished c g.1 s`, `f : Restricted A c` —
    shapes line up with `ℓ`, `f` packaged at radius `c` (needs `[Fact (0 < c)]`,
    provided by `Fact.mk` on `‖a‖ + 1 > 0` — `have := Fact.mk` pattern; note the
    QMF-port lesson: this is a legitimate local instance). (5) `IsMulDistinguished`
    fields not re-read here — the ticket instructs the worker to open
    `MulDistinguished.lean:35` first and verify `ℓ` satisfies each field at
    `c > ‖a‖`; if the structure demands more (e.g. norm-unit leading coefficient),
    fields still satisfy it (`‖a⁻¹‖ ≠ 0`). Verdict: SURVIVED with one recorded
    worker-instruction.
  - Prior-B2: no match.

---

### Cluster O — operator-limit infrastructure (`IsOpLimit`)

- **O1** (leaf, new def + 5 lemmas): `IsOpLimit`, `.unique`, `.add`, `.const`,
  `.comp_left`, `.comp_right`
  - Source: none (infrastructure; Serre works in the Banach algebra `ℒ(E,E)` which
    the repo deliberately does not instantiate — see `OperatorNorm.lean` docstrings:
    "no `SeminormedAddCommGroup` instance on `M →L[R] N`, deliberately").
  - Discharge: `unique` from `norm_add_le`/`opNorm_sub_comm`/`opNorm_eq_zero_iff`
    (squeeze `‖L−L'‖ ≤ ‖L−Tₙ‖+‖Tₙ−L'‖ → 0`); `comp_left/right` from `opNorm_mul_le`
    (`OperatorNorm.lean:528`, needs `[IsTate R]` — signatures verified); `add` from
    `norm_add_le`; all elementary `Tendsto` squeezes.
  - Attacks: (1) `IsOpLimit` vs a `Tendsto`-in-a-topology formulation: no topology
    exists on the hom-type by design — the metric phrasing is the only one available;
    matches `exists_lim_of_cauchySeq`'s output shape exactly (that lemma IS
    `∃ v, IsOpLimit u v`). (2) edge: constant sequences (`.const`), `T = T'`
    aliasing in `.add` — fine. (3) hypothesis: `comp_*` genuinely need `[IsTate R]`
    (through `opNorm_mul_le`'s section) — checked, not over-assumed elsewhere.
    Verdict: SURVIVED.
  - Prior-B2: no match.

### Cluster CC — compactoid closure

- **CC1** (leaf, 10 lemmas): `matrixCoeff_add/neg/sub/smul`, `norm_matrixCoeff_le'`,
  `rowNorm_add_le`, `rowNorm_neg`, `rowNorm_smul_le`, `IsCompactoid.add/neg/sub/smul`
  - Source: [Serre1962] uses these silently (`v = −au + auv` is completely continuous,
    p. 80: "on trouve v = −au + auv, ce qui montre que v est complètement continu");
    the repo has only `comp_left/right` (Explore: closure under `+`, `−`, `•` ABSENT,
    and `matrixCoeff_sub` exists only `private` in `Fredholm.lean:86`).
  - Discharge: `matrixCoeff` is evaluation (`u (single i 1) j`) — additivity is
    `ContinuousLinearMap.add_apply` etc.; `rowNorm_add_le` via
    `Real.iSup_le` + ultrametric `norm_add_le_max`
    (`IsUltrametricDist.norm_add_le_max`) + `BddAbove` from `norm_matrixCoeff_le'`
    (which is `norm_apply_le` + `le_opNorm` + `norm_single_one`, all public);
    `IsCompactoid.*` by `squeeze_zero` against `max`/`‖a‖·` of null sequences
    (`Tendsto.max`, `Tendsto.const_mul`).
  - Attacks: (1) `rowNorm_smul_le` is `≤` not `=` — over a non-multiplicative normed
    ring equality FAILS (‖a·x‖ < ‖a‖‖x‖ possible); statement deliberately one-sided.
    (2) `IsCompactoid.smul` needs no `IsTate` (pure squeeze) but `add` does
    (`BddAbove` via `‖u‖`-bound uses `le_opNorm`'s `[IsTate R]` section) — variable
    placement in skeleton matches. (3) edge: `u = 0`, `a = 0` — all fine
    (`rowNorm 0 = 0` needs `iSup` of zeros = 0, `Real.iSup_const`… `ciSup_const`);
    checked `rowNorm` is an `iSup` over possibly-empty `I` — `I = ∅`: `iSup` over
    empty type is `0` in ℝ ✓ conventions hold. Verdict: SURVIVED.
  - Prior-B2: no match.

---

### Cluster B — the Fredholm resolvent (Serre §6)

- **B1** (leaf): `resolventCoeff`, `resolventCoeff_zero`, `resolventCoeff_succ`,
  `resolventCoeff_sub_mul`
  - Source: [Serre1962, §6 p. 78], verbatim:
    > "La résolvante de Fredholm de u est par définition la série formelle
    > P(t, u) = det(1−tu)/(1−tu) = Σ vₘ tᵐ. Les vₘ sont des éléments de ℒ(E, E). On
    > les calcule au moyen des formules de récurrence [v₀ = 1, vₘ = cₘ + u vₘ₋₁].
    > Ces formules montrent en particulier que les vₘ sont des polynômes en u."
  - Lean ↔ source: we DEFINE `vₘ` by the closed form `Σ_{k≤m} cₖ u^{m−k}` (the solved
    recursion — "polynômes en u" made literal) and prove the recursion as lemmas;
    `resolventCoeff_sub_mul` is the coefficient form of `(1−tu)P = H`.
  - Discharge: `Finset.sum_range_succ`, `pow_succ`, `mul_smul_comm`, ring algebra on
    `M →L[R] M` (Monoid/Ring instances exist — used by `opNorm_pow_le`,
    `Pr.lean`'s `(… )^n`). Grounding: 3 displayed lines in source; ~40 LOC.
  - Attacks: (1) recursion direction: `vₘ = cₘ·1 + u·vₘ₋₁` vs `+ vₘ₋₁·u` — `u`
    commutes with each `vₘ` (polynomials in `u`), both correct; source writes
    `u vₘ₋₁`; our closed form gives either; lemma states the source's. (2) edge
    `m = 0`: `v₀ = c₀·u⁰ = 1` ✓ (`charCoeff_zero`). (3) composition check
    (children→parent): `resolventCoeff_sub_mul` at `m` plus `charPowerSeries_coeff`
    reproduces `(1−tu)P = H` coefficientwise — verified by hand at `m = 0, 1`.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **B2** (internal → 3 leaves): Serre's Lemme 3
  - Source: [Serre1962, §6 p. 79], verbatim:
    > "Lemme 3. — On a |vₘ| ≤ r₁…rₘ. … a) L'espace E est de dimension finie. — Les
    > formules de Cramer montrent que la résolvante de Fredholm P(t, u) a pour matrice
    > la matrice adjointe de 1 − tu : … Le coefficient de tᵐ dans un tel terme est une
    > combinaison linéaire, à coefficients ±1, de mineurs d'ordre m de la matrice
    > (n_{ij}), donc aussi une combinaison linéaire, à coefficients ±1, de produits
    > n_{i₁j₁}…n_{iₘjₘ} où les indices j₁, …, jₘ sont deux à deux distincts. …
    > b) Il existe une partie finie J de I telle que n_{ij} = 0 si j n'appartient pas
    > à J … c) Cas général. — … Quand J varie, les u(J) tendent vers u, de même, les
    > formules de récurrence définissant les vₘ montrent que vₘ(J) → vₘ."
    (Note: Serre's `n_{ij}` indexing makes his "j distincts" our distinct ROWS in the
    repo's `matrixCoeff u j i` convention — consistent with `rowNorm`.)
  - Sub-leaves:
    - **B2a** (leaf): `matrixCoeff_resolventCoeff_of_rows` — the adjugate
      identification, proved by uniqueness of solutions of the recursion: both
      `m ↦ vₘ`-block and `m ↦ coeff m (adjugate (1−tA))` satisfy
      `w₀ = 1, wₘ = cₘ1 + A·wₘ₋₁` (for the adjugate side this is
      `Matrix.mul_adjugate` : `(1−tA)·adj(1−tA) = det(1−tA)·1` read off
      coefficientwise, using `charCoeff_eq_det_coeff` for `det(1−tA) = Σ cₘtᵐ`).
      Discharges: `Matrix.mul_adjugate`, `charCoeff_eq_det_coeff` (verified
      signatures), `Polynomial.coeff_mul`. Also `matrixCoeff_mul_of_rows` (stated in
      cluster C) for operator-vs-matrix product compatibility.
    - **B2b** (leaf): `matrixCoeff_resolventCoeff_of_notMem` — rows off the support:
      `vₘ = cₘ·1` there (recursion + zero rows), `if j = i then cₘ else 0`.
    - **B2c** (leaf): `norm_resolventCoeff_le` — the norm bound, via
      `norm_eq_iSup_matrixCoeff` + entrywise: on-block entries through B2a and the
      Leibniz expansion of `det(updateRow …)` (`Matrix.adjugate_apply`,
      `Matrix.det_apply` sums over permutations; the `tᵐ`-coefficient of each
      permutation product picks `m` distinct non-updated rows) bounded by
      `∏_{j ∈ T} rowNorm u j` for some `T.card = m`; off-block entries are `|cₘ|`,
      bounded by `norm_tsum_le_iSup` + `norm_minor_le_prod` (same shape). The `⨆` on
      the right absorbs both.
  - Attacks (internal node): (1) composition: could B2a+B2b+B2c hold and Lemme 3
    fail? The iSup-form is WEAKER than Serre's sorted `r₁⋯rₘ` (sup over distinct
    `m`-products ≤ sorted top product) — but B3 only needs the iSup form (decay of
    distinct products), so the weakening is safe; recorded as a deliberate deviation.
    (2) `m > |I|` edge (finite `I`): no `m`-subset exists — iSup over empty type
    is `0` in ℝ; entries genuinely vanish? On-block: adjugate of an `n×n` matrix has
    polynomial entries of degree ≤ n−1… for `m ≥ n` the coefficient is 0 ✓; off-block
    `cₘ = 0` for `m > n` (det degree) ✓ — consistent. (3) transpose trap: mathlib
    `adjugate_apply A i j = det (A.updateRow j (single i 1))` — index order checked
    against `mul_adjugate` (`A * adj A = det A • 1`) and our
    `(1−tM)·P-matrix = H·1`: matches with `P-matrix j i = adj j i`; the skeleton
    statement uses `adj … j i` — worker must re-verify orientation on first
    compile (recorded in ticket). (4) `updateRow` vs `updateCol`: if orientation
    flips, use `adjugate_transpose`. Verdict: SURVIVED with two recorded
    worker-checks.
  - Prior-B2 log: no match.

- **B3** (leaf): `tendsto_resolventCoeff_truncation`, `tendsto_norm_resolventCoeff`
  - Source: [Serre1962, §6 pp. 78–79], verbatim:
    > "Proposition 10. — La résolvante de Fredholm P(t, u) est une fonction entière
    > … pour tout nombre réel M, on a lim |vₘ| Mᵐ = 0." and step c): "Quand J varie,
    > les u(J) tendent vers u, de même, les formules de récurrence définissant les vₘ
    > montrent que vₘ(J) → vₘ. On en déduit bien |vₘ| ≤ r₁…rₘ."
  - Lean ↔ source: `tendsto_resolventCoeff_truncation` is exactly step c)'s
    `vₘ(J) → vₘ` with `u(J) := (truncation J).comp u` (row truncation — matches
    Serre's "n'_{ij} = n_{ij} si j ∈ J" in the repo's row convention);
    `tendsto_norm_resolventCoeff` is Prop. 10, deduced from B2c's bound + the repo's
    threshold-split decay pattern (the `δ/D/b` skeleton of
    `charPowerSeries_isEntire`, `Fredholm.lean:203–239`, applies verbatim to
    products over distinct rows).
  - Discharge: `tendsto_truncation_comp` (`Matrix.lean:445`) for `u(J) → u`;
    operator-norm polynomial continuity of `u ↦ vₘ(u)` at fixed `m` (finite sum of
    products; `opNorm_mul_le`, `norm_add_le`, `norm_charCoeff_sub_le` for the
    `cₖ`-dependence); the `δ/D/b` split + `squeeze_zero'` for the decay.
  - Attacks: (1) does B3 even need B2c for the TRUNCATED operators only (then pass
    to the limit), or for `u` directly? Serre: bound for `u(J)` (finite case) + limit
    gives the bound for `u`; then decay. Our skeleton states the bound (B2c) for
    general compactoid `u` — proved via the same limit; composition checked: B2c(u)
    := lim of B2c(u(J)) via B3-truncation — NO circularity: B2c for row-supported
    `u` is finite-case (B2a/B2b only); `tendsto_resolventCoeff_truncation` needs no
    norm bound; then B2c-general = limit of B2c-row-supported. Dependency order in
    tickets reflects this. (2) edge `M ≤ 0`: `Mᵐ` sign — statement quantifies over
    all real `M`; for `M ≤ 0` the sequence is not sign-definite… `‖vₘ‖·Mᵐ`
    oscillates but `|‖vₘ‖Mᵐ| = ‖vₘ‖|M|ᵐ → 0` still forces tendsto-0 ✓ harmless;
    consumers use `M = ‖a‖ ≥ 0` anyway. (3) hypothesis: `IsCompactoid` (not
    completely-continuous) — matches the repo's organising notion; Serre's u is c.c.
    on `c(I)` which the repo shows equivalent under Noetherian, and compactoid is
    the weaker/right hypothesis (strictly more general than source — flagged as
    deliberate strengthening, same as the whole `Fredholm.lean`). Verdict: SURVIVED.
  - Prior-B2: no match.

- **B4** (leaf): `resolventPartialSum`, `exists_isOpLimit_resolventPartialSum`
  - Source: [Serre1962, §7 p. 80]: the operators `ΔˢP(a, u)` exist because "Les
    « dérivées divisées » Δˢ transforment une fonction entière en une fonction
    entière" (verbatim, p. 80).
  - Lean ↔ source: `Nₛ = Σₘ (m+s choose s) aᵐ vₘ₊ₛ`, realised as the `IsOpLimit` of
    partial sums; entireness of `ΔˢP` = the tail estimate
    `‖(m+s choose s)aᵐvₘ₊ₛ‖ ≤ ‖vₘ₊ₛ‖‖a‖ᵐ → 0` (binomials have norm ≤ 1:
    `IsUltrametricDist.norm_natCast_le_one`).
  - Discharge: `exists_lim_of_cauchySeq` (`OperatorNorm.lean:220`); ultrametric
    partial-sum Cauchyness from `opNorm_sum_le` + B3; `norm_natCast_le_one` (mathlib
    ultrametric — verify name at implementation; fallback: induction from
    `norm_add_le_max`).
  - Attacks: (1) `choose`-cast: `((m+s).choose s : R)` via `ℕ → R` cast — smul vs
    mul with `a^m •` — skeleton uses two smuls (`(χ : R) • aᵐ • vₘ₊ₛ`); associativity
    fine (`smul_smul`). (2) edge `s = 0`: `N₀` partial sums = `Σ aᵐvₘ` ✓ matches
    `P(a,u)`. (3) `a = 0`: partial sums stabilise at `v_s` — limit exists trivially ✓
    consistent. Verdict: SURVIVED.
  - Prior-B2: no match.

- **B5** (leaf): `commute_of_isOpLimit_resolventPartialSum`
  - Source: [Serre1962]: implicit in "les vₘ sont des polynômes en u" (p. 78) — Serre
    freely commutes `u` with `P(a, u)` in §7's computations.
  - Discharge: each partial sum commutes with `u` (finite sum of `cₖ • u^j`);
    limits: `u·N` and `N·u` are both `IsOpLimit` of `u·(partial n)` = `(partial n)·u`
    (O1 `.comp_left/.comp_right`), so equal by `IsOpLimit.unique`.
  - Attacks: (1) needs `Commute u (u^j)` — `Commute.pow_right (Commute.refl u)` ✓
    mathlib. (2) smul-commuting: `u * (c • w) = c • (u * w)` — `mul_smul_comm` on
    the CLM ring ✓. (3) composition edge: nothing size-dependent. Verdict: SURVIVED.
  - Prior-B2: no match.

- **B6** (leaves): `one_sub_smul_mul_resolventEval_zero`,
  `one_sub_smul_mul_resolventEval`
  - Source: [Serre1962, §7 pp. 80–81], verbatim (partially garbled in extraction,
    reconstructed):
    > "Considérons alors l'identité : (1−tu).P(t, u) = H(t). En lui appliquant
    > l'opérateur Δˢ, on trouve : (1−tu)ΔˢP(t, u) − uΔ^{s−1}P(t, u) = ΔˢH(t)."
    (The product rule collapses because `Δ⁰(1−tu) = 1−tu`, `Δ¹(1−tu) = −u`,
    `Δ^{≥2}(1−tu) = 0`.)
  - Lean ↔ source: evaluated at `t = a`, with `Nₛ`, `Nₛ₋₁` the `IsOpLimit`s: exactly
    the two skeleton statements (`s = 0` separately since `N₋₁` is absent).
  - Discharge: the COEFFICIENT identity
    `(m+s choose s)vₘ₊ₛ − (m−1+s choose s)u·vₘ₊ₛ₋₁ =
     (m+s choose s)cₘ₊ₛ·1 + (m+s−1 choose s−1)u·vₘ₊ₛ₋₁`
    is 3 lines from `resolventCoeff_succ` + Pascal (`Nat.succ_sub_one`,
    `Nat.choose_symm_diff`/`Nat.choose_succ_succ` — verified during planning by hand:
    with `vₘ₊ₛ = cₘ₊ₛ1 + u vₘ₊ₛ₋₁`, LHS = `χ·cₘ₊ₛ + (χ−χ')u vₘ₊ₛ₋₁` and
    `χ−χ' = C(m+s−1, s−1)` is Pascal). Then multiply by `aᵐ`, sum over `m < n`,
    telescope, and pass to the limit with O1 (`(1−a•u)·` is `IsOpLimit`-continuous
    by `.comp_left`); the scalar side converges to
    `evalT a (hasseDeriv s (charPowerSeries u))` by A1/A2 + B3-derived summability of
    `χ·cₘ₊ₛaᵐ` (charCoeff decay from `charPowerSeries_isEntire`).
  - Attacks: (1) the planning-time Pascal computation was re-derived twice
    (independently in two forms) — consistent; worker re-derives before coding.
    (2) telescoping boundary terms: partial-sum mismatch (the `u·N'` sum runs to
    `n−1` vs `n`) contributes one term `→ 0` — standard; recorded in sketch.
    (3) `s = 0` separately: no `N'`; identity is `vₘ − u vₘ₋₁ = cₘ·1` directly ✓
    `resolventCoeff_sub_mul`. (4) composition to parent (D-cluster): the equations
    at `s ≤ h` are exactly what steps 4–5 consume — checked shape against
    `exists_mem_ker_of_hasseDeriv_evalT`'s hypotheses. Verdict: SURVIVED.
  - Prior-B2: no match.

---

### Cluster C — determinant value and multiplicativity (Serre §5, Cor. 1 + Prop. 8)

- **C1** (leaf): `fredholmDet`, `charCoeff_smul`, `fredholmDet_smul`
  - Source: [Serre1962, §5 p. 76], verbatim:
    > "Le fait que det(1−tu) soit une fonction entière permet de substituer à t
    > n'importe quelle valeur dans K. En particulier, det(1+u) est défini pour tout
    > u ∈ ℒc(E, E)."
  - Lean ↔ source: `fredholmDet u := evalT 1 (charPowerSeries u)` is `det(1−u)`;
    `charCoeff_smul` (`cₙ(a•u) = aⁿcₙ(u)`) is the homothety Serre invokes as "le cas
    général en résulte par homothétie" (p. 75); `fredholmDet_smul` chains it with
    `evalT` reindexing (`(a·1)ⁿ` vs `aⁿ·1ⁿ`).
  - Discharge: minors are `n`-linear in rows: `matrixCoeff (a•u) = a·matrixCoeff u`
    (CC1) + `Matrix.det_smul` (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:272`,
    verified) + `tsum` scalar-mul (`tsum_mul_left`).
  - Attacks: (1) `det_smul` gives `cⁿ·det` with `n = card S` — matches minor of an
    `n`-subset exactly (`S.card = n` in `charCoeff`'s index) ✓. (2) edge `a = 0`:
    `c₀(0•u)=1, cₙ(0) = 0 (n≥1)`; RHS `0ⁿcₙ` ✓. (3) `evalT 1` summability: needs
    `‖cₙ‖·1ⁿ → 0` — from `charPowerSeries_isEntire` at `C = 1` ✓ (`hu` hypothesis
    present in `fredholmDet_smul`; `fredholmDet` def itself is junk-safe). Verdict:
    SURVIVED.
  - Prior-B2: no match.

- **C2** (leaves): `fredholmDet_eq_det_of_rows`, `matrixCoeff_mul_of_rows`
  - Source: [Serre1962, §5 p. 76], Prop. 7 d), verbatim:
    > "d) Si u est de rang fini, det(1−tu) coïncide avec le polynôme défini plus
    > haut."
  - Lean ↔ source: for row-supported `u` the value `H_u(1)` is the polynomial
    determinant `det(1 − A_S)`; the product-of-matrices lemma is the standard
    matrix-of-composition fact needed to convert `(1−u)(1−v)` to matrix form.
  - Discharge: `charCoeff_eq_det_coeff` (`Fredholm.lean:498`, exact hypothesis shape
    `hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0` — matches) + `Polynomial.eval_one` +
    `tsum` of finitely-supported = `Finset.sum` (`tsum_eq_sum`); degree bound: the
    det-polynomial has degree ≤ card S (`Polynomial.natDegree_det_le`-style; if
    missing, coefficient-vanishing from `charCoeff` via minors of card > |S| being 0
    — both routes recorded). `matrixCoeff_mul_of_rows`: `hasSum_single`
    (`ModelSpace.lean:136`) + continuity of `u` + finiteness from `hv`.
  - Attacks: (1) `Matrix.of fun j i : S` orientation — same convention as
    `charCoeff_eq_det_coeff` (copied verbatim from it) ✓. (2) edge `S = ∅`: `u = 0`,
    `fredholmDet 0 = 1 = det(1 : Matrix ∅ ∅)` ✓. (3) the composition lemma quantifies
    the INNER factor's support (`hv` on `v`) — sufficient for both uses
    (`(1−A)(1−B)` with both truncated); checked that C3's finite step only ever
    multiplies row-supported by row-supported. Verdict: SURVIVED.
  - Prior-B2: no match.

- **C0** (leaf): `eventually_norm_charCoeff_sub_le` (Serre Prop. 8)
  - Source: [Serre1962, §5 p. 77], verbatim:
    > "Proposition 8. — Soit (uₙ) une suite d'éléments de ℒc(E, E) convergeant vers
    > un élément u. Alors det(1−tuₙ) → det(1−tu) pour la topologie de la convergence
    > uniforme sur toute partie bornée de la clôture algébrique K̄ de K. … En
    > l'écrivant comme somme de produits de différences, on obtient l'inégalité
    > |n_{S,σ} − n'_{S,σ}| ≤ η·Sup_{i∈S} Π_{j∈S, j≠i} Sup(r_j(u), r_j(uₙ)) …
    > En sommant, on en déduit |cₘ − c⁽ⁿ⁾ₘ| ≤ ε pour tout m."
  - Lean ↔ source: our statement is the coefficient form at radius `M` (`∀ᶠ n, ∀ m,
    ‖cₘ(wₙ) − cₘ(u)‖·Mᵐ ≤ ε`) — precisely "uniform convergence on the disc of
    radius M", which is what the value-convergence at `t = 1` (or any bounded point)
    needs.
  - Discharge: the "somme de produits de différences" is the repo's private
    `norm_det_sub_det_le` (`Fredholm.lean:273`: `‖A.det − B.det‖ ≤ M^(card−1)·ε`
    row-telescoping — same technique; worker adapts with rowNorm-products instead of
    a global `M`, or re-proves the sharper product form locally); the finitely-many-
    large-rows bookkeeping is the repo's `δ/D/b` threshold pattern; `IsCompactoid`
    supplies the decay.
  - Attacks: (1) Serre states it over K̄-bounded sets; we state the coefficient
    inequality over ℝ-radius `M` — strictly the same content for our use (no
    algebraic closure needed) — drift is a deliberate weakening, safe. (2) edge
    `M ≤ 1` vs `M > 1`: the `Mᵐ` factor is why the naive `norm_charCoeff_sub_le`
    (`max‖·‖^{n−1}·‖u−v‖`) is insufficient at `M ≥ 1/max‖·‖` — the attack CONFIRMED
    the naive bound fails (`‖u‖ > 1`, `M = 1`: `max^{m−1}` diverges), which is
    exactly why C0 exists as its own leaf; this attack was run during planning and
    killed an earlier "reuse `norm_charCoeff_sub_le` alone" draft. (3) hypothesis:
    all `wₙ` compactoid — needed for their coefficient decay; supplied at both use
    sites (truncations are compactoid via `comp_left`… actually finite-rank rows:
    row-truncations of a compactoid are compactoid by `rowNorm` domination — worker
    note). Verdict: SURVIVED (one planning-time attack succeeded and reshaped the
    plan — recorded).
  - Prior-B2: no match.

- **C3** (leaf): `fredholmDet_mul`
  - Source: [Serre1962, §5 p. 76], verbatim:
    > "Corollaire 1. — Si u et v appartiennent à ℒc(E, E), on a
    > det(1+u+v+uv) = det(1+u).det(1+v). On a plus généralement
    > det((1−tu)(1−tv)) = det(1−tu).det(1−tv), comme on le voit en se ramenant au
    > cas où |u| ≤ 1, |v| ≤ 1, et en réduisant modulo 𝔞."
  - Lean ↔ source: at `t = 1` with the sign convention `1−(u+v−uv) = (1−u)(1−v)`
    (Serre's display is the `+`-form; ours is the same statement for `−u, −v` —
    checked: `det(1+(−u)+(−v)+uv)` = our LHS). Serre's mod-𝔞 reduction is replaced
    by the truncation-limit: same-`S` row-truncations `π_S u, π_S v`, finite case by
    C2 + `Matrix.det_mul`, limit by C0 (both `π_S u ⊞ π_S v → u ⊞ v` in operator
    norm — via `tendsto_truncation_comp` + CC1 + `opNorm` algebra — and coefficient
    uniformity).
  - Discharge: C0, C2, CC1, `Matrix.det_mul` (verified), `tendsto_truncation_comp`.
  - Attacks: (1) `π_S u ⊞ π_S v` is row-supported in `S`: rows off `S` of the sum
    and of the product vanish (`e_j ∘ π_S = 0` off `S`) ✓ checked pointwise.
    (2) does `π_S u ⊞ π_S v → u ⊞ v` in OPERATOR norm? `‖π_Su∘π_Sv − u∘v‖ ≤
    ‖π_Su‖‖π_Sv − v‖ + ‖π_Su − u‖‖v‖` with `‖π_Su‖ ≤ ‖u‖` (truncation
    norm-decreasing) ✓ and `tendsto_truncation_comp` twice — but C0 is stated for
    ℕ-sequences while truncations are `Finset I`-indexed: bridge by a cofinal
    ℕ-indexed sequence of finsets (choose `S n` increasing exhausting the
    `rowNorm`-bad sets; `atTop` on `Finset I` restricted along a monotone cofinal
    map) — a small bridging argument the ticket records; alternatively restate C0
    over an arbitrary filter — resolved at ticket level, both routes viable.
    (3) sign/`⊞`-orientation: verified `1−(u+v−uv) = (1−u)(1−v)` by ring in the CLM
    ring (needs commutativity? NO: `(1−u)(1−v) = 1−u−v+uv` — u·v order matters;
    our statement uses `u*v` in that order ✓ matches. (4) value-level vs
    series-level: Serre's series-level identity is stronger; we take only `t = 1` —
    all downstream uses (D2) need only that ✓ scope-minimal. Verdict: SURVIVED.
  - Prior-B2: no match.

---

### Cluster D — Riesz theorems

- **D1** (leaf): `isUnit_one_sub_smul_of_isUnit_evalT`
  - Source: [Serre1962, §7 p. 80], verbatim:
    > "Proposition 11. — Soit a un élément du corps K. Pour que 1−au soit inversible
    > dans ℒ(E, E), il faut et il suffit que H(a) ≠ 0. Si H(a) ≠ 0, la relation
    > H(a) = (1−au).P(a, u) = P(a, u).(1−au) montre que 1−au est inversible."
  - Lean ↔ source: `IsUnit`-phrasing over `R` (unit ⟺ ≠0 over the field — strictly
    more general, Buzzard-style); the displayed relation is B6 (`s = 0`) + B5.
  - Discharge: B4 (get `N₀`), B6-zero, B5, `isUnit_of_mul_eq_one` on the CLM ring
    (two-sided via commutation).
  - Attacks: (1) over `R`, `IsUnit (evalT …)` vs `≠ 0`: unit is the correct ring
    hypothesis (Buzzard p. 22 "(ΔʰH)(a) is a unit") — field corollary recovers ≠0.
    (2) `IsUnit` in the NONunital…: CLM ring is unital ✓. (3) two-sidedness: right
    inverse `H(a)⁻¹N₀` + commutation (B5) upgrades — checked `Commute` gives both.
    Verdict: SURVIVED.
- **D2** (leaf): `isUnit_evalT_of_isUnit_one_sub_smul`
  - Source: [Serre1962, §7 p. 80], verbatim:
    > "Réciproquement, supposons que 1−au soit inversible, et écrivons son inverse
    > sous la forme 1−v. En écrivant que (1−au)(1−v) = 1 on trouve v = −au+auv, ce
    > qui montre que v est complètement continu. Le déterminant det(1−v) est donc
    > défini, et le corollaire 1 à la proposition 7 montre que
    > det(1−au).det(1−v) = 1, ce qui démontre que det(1−au) ≠ 0."
  - Lean ↔ source: verbatim transcription: `v := 1 − w` for the inverse `w`;
    `v = −(a•u) + (a•u)*v` compactoid by CC1 + `comp_left/right` + `.smul`;
    `fredholmDet_mul` (C3) with `(a•u) ⊞ v = 0` (ring identity from
    `(1−a•u)(1−v) = 1`); `fredholmDet (a•u) = evalT a H` by C1; conclude
    `IsUnit` from `x·y = 1` in the commutative ring `R` (`isUnit_of_mul_eq_one`).
  - Attacks: (1) `⊞ = 0` check: `(1−x)(1−y) = 1 ⟹ x+y−xy = 0` ✓ ring. (2)
    `fredholmDet 0 = 1`: `charCoeff 0 n = if n=0 then 1 else 0` — needs tiny lemma
    (charCoeff of 0 via minors of the zero matrix; `Matrix.det_zero`… det of 0-matrix
    on nonempty S is 0, on empty S is 1) — recorded as proof-internal step.
    (3) planning-time alternative-route attack: a direct truncation proof of D2
    without C3 was attempted and FAILED (limit of nonzero dets can vanish — no
    quantitative lower bound); confirms C3 is load-bearing; recorded. Verdict:
    SURVIVED.
- **D2'** (assembly): `isUnit_one_sub_smul_iff_isUnit_evalT` — one-line `⟨D2, D1⟩`
  (marked assembly node; iff of the two directions).
- **D3** (leaf): `exists_mem_ker_of_hasseDeriv_evalT`
  - Source: the eigenvector content of [Serre1962, §7 Prop. 12] (verbatim statement
    quoted in the plan; its full projector construction is NOT transcribed) run
    through [Buzzard2007, pp. 22–23]'s order definition, verbatim:
    > "We say that a ∈ A is a zero of order h of H ∈ A{{T}} if (ΔˢH)(a) = 0 for
    > s < h and (ΔʰH)(a) is a unit."
  - Lean ↔ source: the dichotomy proof (plain-English step 5) — by cases on
    `∃ x ≠ 0, (1−a•u)x = 0`; in the injective case derive `IsUnit (1−a•u)` from the
    B6-equations (`N₀ = 0` from `(1−au)N₀ = 0` + injectivity as operators, upward
    induction, then `(1−au)N_h = ΔʰH(a)·1` with unit scalar and B5-commutation),
    then D2 + `h0 0` (i.e. `H(a) = 0`, since `hasseDeriv 0 = f`) contradict
    (`IsUnit 0` is false in a nontrivial ring — `Nontrivial R` from `NormOneClass` +
    norm axioms… recorded: use `one_ne_zero` availability; `NormedCommRing` +
    `NormOneClass` gives `‖1‖ = 1 ≠ 0` so `Nontrivial` — small step).
  - Attacks: (1) "injective ∘ N = 0 ⟹ N = 0": `(1−au)(N x) = 0 ∀x` ⟹ `N x = 0` —
    needs injectivity as a function, i.e. `Function.Injective`; phrasing of the
    dichotomy: `¬(∃ x ≠ 0, …)` ⟹ injective: kernel-trivial ⟹ injective for linear
    maps (`sub` trick) ✓. (2) `h = 1` minimal case traced fully by hand during
    planning (N₀ = 0 directly, then `(1−au)N₁ = uN₀ + Δ¹H(a) = unit·1`) ✓.
    (3) zero-divisor trap over `R`: the induction uses only operator composition and
    unit-scalars — no division by non-units; checked each step. (4) shape-match
    against Buzzard Prop. 3.2's proof (which instead builds projectors): ours is
    weaker (kernel only) but sufficient for the goal — deliberate scope reduction,
    recorded in plan. Verdict: SURVIVED.
- **D4/D5/D6** (field assembly): `exists_eigenvector_of_evalT_charPowerSeries_eq_zero`,
  `evalT_charPowerSeries_eq_zero_iff`,
  `exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero`
  - Source: assembly of A4 (+`charCoeff_zero` for `c₀ = 1`) + D3 + D1;
    [Buzzard2007, p. 32] for the slogan ("The spectral variety is a geometric object
    parametrising, in some sense, the reciprocals of the non-zero eigenvalues of φ");
    `charPowerSeries_conj` (`Fredholm.lean:960`) for the transport.
  - Lean ↔ source: `u x = a⁻¹ • x ⟺ (1−a•u)x = 0` given `a ≠ 0` (field algebra);
    converse direction: eigenvector ⟹ non-injective ⟹ `¬IsUnit (1−a•u)` ⟹ (D2')
    `¬IsUnit (evalT …)` ⟹ `= 0` (field: nonzero ⟹ unit).
  - Attacks: (1) `IsUnit` of a CLM vs bijectivity: an operator with nontrivial
    kernel is not left-invertible ✓ (apply to kernel element). (2) `conj` statement
    orientation: matched against `charPowerSeries_conj`'s exact composition shape
    (φ ∘ u ∘ φ.symm), eigenvector transports x := φ.symm y ✓; `IsBoundedSMul K E`
    instances in scope ✓ skeleton compiles. (3) `a ≠ 0` really needed: at `a = 0`,
    `evalT 0 H = c₀ = 1 ≠ 0` — hypothesis-free conjunct, so the headline RETURNS
    `a ≠ 0` rather than assuming it ✓ stronger statement. Verdict: SURVIVED.
  - Prior-B2 (all D): no match.

## API gaps

None. Every leaf is discharged from mathlib (verified names), the TateFredholm/
ForMathlib corpus (verified signatures), or is a bounded new-content leaf whose proof
the source gives in ≤ 1 page and which decomposes no further.

## Confidence gate (Step 5)

1. Every leaf discharged or bounded-new with source proof ✓
2. Skeleton compiles, sorries only ✓ (2319 jobs, 0 errors)
3. Verbatim quote + match paragraph per leaf ✓
4. Adversarial pass with ≥3 attacks per leaf, two successful planning-time attacks
   reshaped the plan (C0's necessity; D2's dead-end alternative) and are recorded ✓
5. Prior-B2 log consulted; no matches ✓
6. Tree mirrors Serre §§5–7 structure (Prop. 8, Prop. 10/Lemme 3 steps a–c, Prop. 11
   both directions, Prop. 12's mechanism; Buzzard p. 22 for the order framework);
   deviations recorded: iSup-form of Lemme 3 (weaker, sufficient), value-level Cor. 1
   (scope-minimal), kernel-only Prop. 12 (scope-minimal), Gauss-norm termination in
   A4 (replaces Buzzard's Noetherian context; uses the project's own Weierstrass
   division) ✓
7. Single-conclusion statements throughout; `D2'` and the two field headlines are
   marked assembly nodes (iff / conjunction of independently-proved parts with
   one-line assembly); the `a ≠ 0 ∧ ∃ …` conjunction in the headline is a
   shared-context bundle kept deliberately (the `a ≠ 0` is needed to even state the
   eigenvalue `a⁻¹` — justification: statement-splitting exception, the parts are
   not independently consumable) ✓

---

## EXTENSION (2026-08-04, user-approved): Serre's full Riesz decomposition

Two tiers added on user request.  Skeleton extended (same file), `lake build` clean,
sorries only — re-verified.  New verbatim source: Serre p. 81, extracted in full.

### Cluster P — the Riesz projectors (Tier 1, over `R`)

- **P1** (leaf): `exists_rieszProjection`
  - Source: [Serre1962, §7 p. 81], verbatim:
    > "Posons vₛ = ΔˢP(a, u). En faisant t = a dans les identités précédentes, on
    > obtient les relations : (1−au)v₀ = 0 ; (1−au)v₁ − uv₀ = 0 ; … ;
    > (1−au)v_h − uv_{h−1} = c, avec c ≠ 0. On en déduit, par récurrence sur s, que
    > (1−au)^{s+1}vₛ = 0 pour s < h. D'autre part, si l'on pose :
    > e = c⁻¹(1−au)v_h et f = −c⁻¹u v_{h−1}, la dernière équation montre que
    > e + f = 1. De plus, on a : f·eʰ = 0, puisque (1−au)ʰv_{h−1} = 0. [Noter que,
    > puisque les vₛ sont des séries de puissances de u, tous les endomorphismes
    > considérés commutent entre eux.] En développant l'équation (e+f)ʰ = 1, on
    > trouve : eʰ + (h·e^{h−1}f + … + h·e·f^{h−1} + fʰ) = 1. Posons alors :
    > p = eʰ, q = h·e^{h−1}f + … + fʰ. On a p + q = 1 et pq = 0 puisque f·eʰ = 0.
    > Il s'ensuit que p² = p, q² = q."
  - Lean ↔ source: `c := (ΔʰH)(a)` is a **unit** (our ring-level hypothesis; Serre's
    `c ≠ 0` over a field), `e := hunit.unit⁻¹ • ((1−a•u) * N_h)`,
    `f := -(hunit.unit⁻¹ • (u * N_{h−1}))`; the ∃-statement bundles `p := eʰ` and the
    inverse-witness `w := (hunit.unit⁻¹)ʰ • ((1−a•u)^{h−1} * N_hʰ)` (Serre p. 81:
    "son inverse étant c^{−h}(1−au)^{h−1}v_hʰ", coefficientwise the same); shared-
    witness existential justified: the six properties define the same pair.
  - Discharged by: T011 (the `Nₛ`), T012 (the equations), the chain
    `(1−au)^{s+1}Nₛ = 0` (induction from the equations + commuting, as quoted),
    binomial expansion `Commute.add_pow` (mathlib, for commuting `e f`), ring algebra.
  - Attacks: (1) `p*q = 0 ⟹ p² = p`: `p = p(p+q) = p² + pq` ✓ re-derived; needs
    `q*p = 0` too — commuting ✓. (2) edge `h = 1`: `p = e`, `q = f`, `f·e = 0` from
    `(1−au)v₀ = 0` ✓ traced by hand. (3) unit-vs-nonzero: over `R` we NEED `c` a unit
    (Serre's field `c ≠ 0`); this is exactly the `hunit` hypothesis — no drift.
    (4) `Commute.add_pow` exists in mathlib (verify at compile; fallback:
    `(e+f)^h = 1^h` and expand by induction). Verdict: SURVIVED.
  - Prior-B2: no match.
  - **RESOLVED 2026-08-04 (T021, sorry-free, std axioms)**: proved, but the binomial
    expansion was DROPPED. `e + f = 1` means `f = 1 - e`, so Serre's `f·eʰ = 0` reads
    `e^{h+1} = eʰ`; induction gives `e^{h+k} = eʰ`, hence `p² = e^{2h} = eʰ = p` directly.
    This is strictly better here because `Commute (N h) (N (h-1))` is NOT available
    (T011 only gives `Commute u (N s)`), which the term-by-term binomial argument would
    have wanted. Nilpotency similarly avoids `geom_sum` (`1 - e^{j+1} = (1-eʲ) + eʲ(1-e)`).

- **P2** (leaves): `ker_one_sub_smul_pow_of_rieszProjection`,
  `range_one_sub_smul_pow_of_rieszProjection`, `isTopCompl_range_one_sub_range_of_isIdempotent`
  - Source: [Buzzard2007, p. 23], verbatim:
    > "The decomposition is visibly unique, as if ψ = (1−aφ)ʰ then N = ker(ψ) and
    > F = Im(ψ)."
    and [Serre1962, p. 81]: "On a (1−au)ʰq = 0, ce qui montre que 1−au est nilpotent
    sur N(a); de même, la formule (1−au)ʰ⁺¹?v_hʰ = cʰp montre que 1−au est inversible
    sur F(a)".
  - Lean ↔ source: `ker ψ = range (1−p)`: (⊇) from `ψ(1−p) = 0`; (⊆) `x ∈ ker ψ`:
    `p x = wʰψx`-type computation — from `(1−au)w = p` and commuting,
    `p = pʰ?`… concretely `pˣ = wʰ ψ x`-shape: `p = ((1−au)w)`, so
    `p^h = (1−au)^h w^h = ψ wʰ` ⟹ `p x = p^h x = wʰ (ψ x) = 0` ⟹ `x = (1−p)x` ✓
    (uses `p` idempotent). Range version dual. Topological complement: mathlib
    `ContinuousLinearMap.IsIdempotentElem.isTopCompl` (verified present at
    `Mathlib/Topology/Algebra/Module/Complement.lean`) + `ker (1−p) = range p` for
    idempotents (mathlib `IsIdempotentElem` CLM file; else 3-line argument).
  - Attacks: (1) the `p x = wʰ ψ x` identity re-derived twice ✓. (2) edge `h = 0`
    excluded by `hh : 1 ≤ h` where needed; the `isTopCompl` lemma is `h`-free ✓.
    (3) closedness: comes from `Submodule.IsTopCompl.isClosed` (Hausdorff ✓ metric) —
    no separate leaf needed (skeleton drops the two redundant decls after the
    mathlib discharge was found — recorded). Verdict: SURVIVED.
  - Prior-B2: no match.
  - **RESOLVED 2026-08-04 (T022, sorry-free, std axioms)**: exactly as planned. Note
    `p^h = p` is proved WITHOUT `1 ≤ h` (for `h = 0`, `hnil` itself forces `p = 1 = p⁰`),
    so both characterisations hold at EVERY exponent — which is what makes P3's
    common-exponent step free. No CLM-level idempotent ker/range-swap lemma exists in
    mathlib; the 3-line double inclusion was used, as the fallback anticipated.

- **P3** (leaf): `rieszProjection_unique`
  - Source: Serre p. 81 "son unicité est immédiate" + Buzzard's characterisation
    (above).
  - Lean ↔ source: both projectors have kernel/range characterised by P2 at their own
    orders; `ker ψ^m` and `range ψ^m` are constant for `m ≥ h` (on `range p`, `ψ` is
    invertible via `w`, so no new kernel appears; on `range (1−p)`, already killed) —
    hence the characterisations at `h` and `h'` agree at `h + h'`, and two continuous
    idempotents with equal range and equal kernel are equal (`x = px + (1−p)x`
    decomposition argument).
  - Attacks: (1) stabilisation argument re-derived: `ker ψ^{h+1} ⊆ ker ψ^h`: for
    `x ∈ ker ψ^{h+1}`, `ψx ∈ ker ψ^h ∩ range ψ`?? — corrected route: use the P2
    characterisations directly: `ker ψ^m = range (1−p)` for ANY `m ≥ h` (same proof:
    `p = ψ^m wᵐ`) ✓ no stabilisation lemma needed — plan simplified during attack.
    (2) idempotent-equality: `p' = p'·(p + (1−p))`, `p'p = p` computations — needs
    `p p' = p' p`?? NOT given! Attack FOUND A GAP: two idempotents with same
    range/kernel are equal WITHOUT commuting: `p'x = p'(px + (1−p)x) = p'(px)`;
    `px ∈ range p = range p'` ⟹ `p'(px) = px`; and `p'((1−p)x) = 0` since
    `(1−p)x ∈ ker p'`?? `range (1−p) = ker p`… need `range(1−p') = range(1−p)` ⟹
    `(1−p)x ∈ range(1−p') = ker p'` ✓ (for idempotent `p'`, `range (1−p') = ker p'`
    — standard). So `p' x = p x` ✓ pointwise, no commuting — gap closes; proof
    recorded. Verdict: SURVIVED (one attack found and repaired a gap in the plan).
  - Prior-B2: no match.
  - **RESOLVED 2026-08-04 (T023, sorry-free, std axioms)**: the REPAIRED argument was
    needed as written and was used verbatim — `p` and `p'` are never assumed to commute.
    The common-exponent step is 4 lines (`pow_add` + `mul_assoc` + `hnil`/`hnil'`), because
    all of `hp, hup, hpw, hw, huw` are exponent-free and P2 holds at every exponent.
    `hh`/`hh'` turned out to be unused.

- **P4** (leaf, field): `finite_ker_one_sub_smul_pow`
  - Source: [Serre1962, p. 81]: "la dimension de N(a) est finie" (via his W-argument);
    our route is Buzzard's ([Buzzard2007, p. 23], verbatim):
    > "It is clear that N satisfies (Pr), but furthermore we have (1 − aφ)ʰ = 0 on N
    > which implies that the identity is compact on N. An elementary argument …
    > shows that if β ∈ Hom(N,N) has sufficiently small norm, then |βⁿ| → 0 and
    > hence 1 − β is invertible. Because 1 is compact, we can choose α : N → N of
    > finite rank such that 1 − α is sufficiently small, and hence α is invertible
    > and so N is finitely-generated."
  - Lean ↔ source: run on `N := ker ψ` (closed ⟹ complete Banach); `1_N` is a
    polynomial in `(a•u)|_N`-compressions (finite Neumann sum of the nilpotent
    `1 − (a•u)`), compressions `q∘v∘incl` of finite-rank approximants stay
    finite-rank ⟹ `1_N` completely continuous; pick finite-rank `α` with
    `‖1 − α‖ < 1`; Neumann (`exists_inverse_of_norm_id_sub_lt_one`, needs
    `CompleteSpace N` ✓ closed subspace) ⟹ `α` invertible ⟹ `id` finite-rank ⟹
    `N` f.g. ⟹ finite-dimensional over the field.
  - **Deviation recorded**: `Pr.lean`'s `finite_projective_of_one_sub_compact_nilpotent`
    is NOT reused: its `HasPr` demands a model-space index that is a *subset of the
    module*, and a small `N` inside a large `c(I,K)` need not admit one (cardinality
    obstruction found during planning — attack on the discharge). The Buzzard
    argument is run directly instead; the docstring records this.
  - Attacks: (1) the `HasPr` cardinality obstruction (found; rerouted — this attack
    SUCCEEDED against the original discharge plan). (2) restriction of
    `IsCompletelyContinuous` to a closed invariant complemented subspace: the
    compression `π∘v∘ι` of finite-rank is finite-rank (`IsFiniteRank.comp_left/right`
    exist, `Compact.lean:43,51`) ✓; norms compatible (induced) ✓. (3) f.g. ⟹
    `Module.Finite` over `K` ✓ (`Module.Finite.iff_fg`). Verdict: SURVIVED.
  - Prior-B2: no match.
  - **RESOLVED 2026-08-04 (T024, sorry-free, std axioms)**: run exactly as planned on
    `N = ker ψ`; `Pr.lean` untouched (the recorded `HasPr` obstruction stands). Attack (2)'s
    "norms compatible (induced)" was right but incomplete: `IsBoundedSMul K ↥N` is **not** an
    instance in mathlib and had to be supplied by `IsBoundedSMul.of_norm_smul_le`
    (`Submodule.coe_norm` is `rfl`, so it is a one-liner); `CompleteSpace ↥N` is
    `ψ.isClosed_ker.completeSpace_coe`. The compression `π∘T∘ι` needed one reusable
    coordinate lemma (`↑((π ∘SL T ∘SL ι) y) = T ↑y` for `N`-stable `T`), from which
    `ν`, `τ`, `ν^k` and `1_N = τ·Σν^k` are pure bookkeeping. `Module.Finite` came out as
    `⟨hQtop ▸ hQfg⟩` rather than through `Module.Finite.iff_fg`.

### Cluster Q — `dim N(a) = h` (Tier 2, field + discreteness where noted)

- **Q1** (leaf): `hasseDeriv_order_unique`
  - Source: implicit in [Buzzard2007, p. 22] (the order is well-defined).
  - Discharge: trichotomy on `h, h'`; if `h < h'` then `hh` contradicts `h0' h hh'`?
    — precisely: `h < h'` gives `evalT a (Δʰf) = 0` from `h0'`, contradicting `hh`.
    Two lines. Attacks: (1) needs no nontriviality (`hh` is `≠ 0`, direct
    contradiction) ✓. (2) symmetric case ✓. (3) `h = h'` base ✓. SURVIVED.
- **Q2** (leaf): `det_one_sub_X_smul_of_isNilpotent`
  - Source: [Serre1962, p. 81]: "det(1 − tu_W) = (1 − ta⁻¹)^{dim W}" (for
    `1 − au` nilpotent on `W`).
  - Discharge: over the field `K`: `1 − a•A` nilpotent ⟹ `A = a⁻¹(1 − N)` with `N`
    nilpotent ⟹ `det(1 − tA) = det((1 − ta⁻¹)·1 + ta⁻¹N)`; substitute/scale:
    charpoly of nilpotent `N` is `Xⁿ` (mathlib `Matrix.IsNilpotent.charpoly`?
    verify — else triangularization-free route: `det(1 − sN) = 1` for all `s` since
    `1 − sN` unipotent (det of unipotent = 1: `Matrix.det_unipotent`?; fallback:
    `IsNilpotent.isUnit_one_sub` + det via `Matrix.det_one_add_smul`-style
    polynomial identity: `det(1 − sN)` is a polynomial in `s` with all coefficients
    beyond 0 killed by nilpotency — worker searches; the identity
    `det (1 − sN) = 1` for nilpotent `N` is the crux and is classical).
    Then `det(1 − tA) = (1 − ta⁻¹)ⁿ · det(1 − s(t)N)`-shape with the scaling
    absorbed — worker works in `Polynomial K` localised at the unit
    `(1 − ta⁻¹)`?? Cleaner route recorded in the ticket: evaluate at the generic
    point via `Matrix.det_smul` + factor `(1 − ta⁻¹)` out of each row of
    `1 − tA = (1−ta⁻¹)·1 + ta⁻¹N`… the worker has freedom; the statement is
    the classical fact and is TRUE (attack: `n = 1`: `A = (a⁻¹)`, det = `1 − ta⁻¹`
    ✓; `A` non-diagonalisable Jordan-ish over `K` ✓ still holds).
  - Attacks: (1) `a ≠ 0` needed (else `a⁻¹` junk; nilpotent `1 − 0` = 1 impossible
    for `n ≥ 1` — statement safe but keep `ha`) ✓. (2) `n = 0`: empty matrix,
    `det = 1 = (…)⁰` ✓. (3) convention check: our LHS matches
    `charCoeff_eq_det_coeff`'s polynomial exactly (copied shape) ✓. SURVIVED.
  - **RESOLVED 2026-08-04 (T025, sorry-free, std axioms)**: 33 lines, and **neither** the
    "det of unipotent = 1" crux nor the `reverse` bookkeeping was needed. `charpoly` is used
    *evaluated*, not reversed: `M := X·(A − a⁻¹)` is nilpotent over `K[X]`, so
    `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent` + `IsNilpotent.eq_zero` (valid
    because `K[X][X]` is a **domain**, hence reduced) gives `M.charpoly = X^n`; then
    `1 − X·A = scalar (1 − C a⁻¹ X) − M` entrywise and `Matrix.eval_charpoly` finishes.
    The reduced-ring hypothesis is essential — the fact is false over `ℤ/4` (`M = (2)`), so
    the field fence is not cosmetic. Bonus: the LHS is *definitionally* `Matrix.charpolyRev A`.
- **Q3** (leaves): `isCompactoid_of_comp_embedding`, `charPowerSeries_blockTriangular`
  - Source: [Serre1962, §5 p. 77], Lemme 2, verbatim:
    > "Lemme 2. — Soit I = I′ ∪ I″ une partition de I. Soit u un endomorphisme
    > complètement continu de E = c(I) qui applique E′ = c(I′) dans lui-même. Soit u′
    > la restriction de u à E′ et soit u″ l'endomorphisme de E″ = c(I″) défini par
    > passage au quotient par u. Alors u′ et u″ sont complètement continus, et l'on a
    > det(1−tu) = det(1−tu′)·det(1−tu″). Cela résulte immédiatement de la
    > définition."
  - Lean ↔ source: hypothesis-style block operators (`u₁`, `u₂` given by their
    matrix coefficients through the subtype inclusions) avoid defining
    restriction/quotient operators; "résulte immédiatement de la définition" = the
    minors factor: a minor over `S ⊆ I` with the triangularity splits as
    `minor(S ∩ P) · minor(S ∩ ¬P)` (`Matrix.det_fromBlocks_zero₂₁` after reindexing
    `S ≃ (S∩P) ⊕ (S∩¬P)`), and the `tsum` over `S` of card `n` Fubini-splits over
    pairs `(S₁, S₂)` with `card S₁ + card S₂ = n` — matching
    `PowerSeries.coeff_mul`'s antidiagonal.  (The Jacobs board proved an equivalent
    `charPowerSeries_partition` — CANNOT import their file; independent local proof.)
  - Attacks: (1) triangularity direction: Serre preserves `E′` = `c(I′)`;
    matrix condition `P i → ¬P j → u_{ji} = 0` says columns in `P` have no
    components outside `P` ✓ matches "applique E′ dans lui-même" with `I′ = P`.
    (2) `u₂` well-defined as "quotient": in matrix terms just the `¬P`-block ✓ our
    hypothesis-form sidesteps the quotient. (3) compactoid of blocks: Q3's first
    lemma (embedding domination: `rowNorm v j ≤ rowNorm u (e j)` + cofinite
    comap along an injection ✓ `Function.Embedding` + `Filter.comap_cofinite`-
    injectivity lemma — verify name `Filter.comap_cofinite_le`… worker searches;
    the mathematical content is: injective preimage of a cofinite-null family is
    cofinite-null ✓ true). (4) tsum Fubini: both index families summable
    (`summable_minor`) — product/sigma reindex via `Summable.tsum_sigma`-family ✓
    exists in mathlib. SURVIVED.
  - **RESOLVED 2026-08-04 (T026, sorry-free, std axioms)**: both leaves proved
    independently of the Jacobs board. Attack (3)'s name search resolves to
    `Function.Injective.tendsto_cofinite` (`Order/Filter/Cofinite.lean:256`) — no
    `comap_cofinite_eq` needed. The `fromBlocks` reindexing of step 2 was replaced wholesale
    by mathlib's **`Matrix.twoBlockTriangular_det`**, which is already stated on the
    subtype-indexed blocks `toSquareBlockProp` and whose triangularity hypothesis matches
    `htri` argument-for-argument (internally it is `det_fromBlocks_zero₂₁`, confirming the
    orientation guess). Attack (4)'s `tsum` Fubini was done WITHOUT a dependent sigma:
    `Equiv.subtypeEquiv (blockEquiv P).symm` moves the sum to the pair index type and
    `HasSum.tsum_fiberwise` over the **Fintype** base `↥(antidiagonal n)` does the split,
    each fibre being a product handled by `Summable.tsum_mul_tsum`. One unforeseen
    elaboration trap: matching a `Summable (fun x : ι × κ => F x.1 * G x.2)` lemma against a
    goal whose two index types differ makes the unifier unfold `Finset.sum`/`Multiset.foldr`
    and diverge — `Summable.congr … fun _ => rfl` is the fix.
- **Q4** (leaf): `charPowerSeries_eq_pow_mul_of_riesz`
  - Source: [Serre1962, p. 81], verbatim:
    > "Appliquant encore le lemme 2, on obtient det(1−tu) = (1−ta⁻¹)^{dim N} H′(t),
    > où H′(t) est le déterminant de Fredholm de la restriction de u à F(a). D'après
    > la proposition 11, on a H′(a) ≠ 0."
  - Lean ↔ source: conjugate `c(I,K)` to `c(Fin d ⊕ s, K)` adapted to `N ⊕ F`:
    `N` finite-dimensional (P4) with a basis giving `N ≃L c(Fin d, K)` (continuity
    of coordinates on a finite-dimensional space over a complete field —
    mathlib `LinearMap.continuous_of_finiteDimensional` /
    `ContinuousLinearEquiv.ofFinrankEq`-family); `F` closed in the Banach `c(I,K)`
    ⟹ Banach, and `isPotentiallyONable_of_uniformizer` (`BaseChange.lean:609`,
    hypothesis `hd` — hence the discreteness hypothesis on this leaf) gives
    `F ≃L c(s, K)`; glue to `Φ : c(Fin d ⊕ s, K) ≃L c(I,K)` via
    `Submodule.prodEquivOfIsTopCompl` (mathlib Complement.lean — verified in the
    import) + a model-space lemma `c(A, K) × c(B, K) ≃L c(A ⊕ B, K)` (small local
    lemma; coordinates); the conjugated operator is block-DIAGONAL (both parts
    `u`-stable), compactoid (`charPowerSeries_conj` transports the char series;
    blocks compactoid by Q3's embedding lemma); apply Q3 + Q2 (the `N`-block:
    `1 − a•(block)` nilpotent by P2's `ψ`-characterisation) + T017(⟸ on the
    `F`-block: `1−a·u₂` invertible — from `w` compressed to `F` — gives
    `evalT a H' = fredholmDet (a•u₂)` a unit ⟹ `≠ 0`).
  - Attacks: (1) THE assembly-order trap: `H'`'s nonvanishing needs Prop 11 on the
    `F`-block, whose compactoidness and invertibility must be established — both
    supplied (Q3-lemma; `w`-compression is a two-sided inverse on `F` by P2) ✓
    chain checked link-by-link. (2) `d = 0` edge (`h` forces `d = h ≥ 1` — but Q4
    is stated BEFORE knowing `d = h`; `d = 0` would make the factor trivial and
    `H' = H` with `H(a) = 0` contradicting `H'(a) ≠ 0` — is Q4 then false?? NO:
    `d ≥ 1` is derivable inside the proof (the dichotomy T018 gives a kernel
    element, so `N ≠ 0`) — ATTACK CAUGHT a potential vacuity; the proof must (and
    can) use T018; recorded in the ticket. (3) discreteness scope: `hd` matches
    `BaseChange.lean`'s exact hypothesis shape (copied) ✓; general-`K` version
    deferred (would need the (Pr)-determinant — out of scope, recorded).
    SURVIVED (one attack strengthened the proof plan).
  - **RESOLVED 2026-08-05 (T028, sorry-free, standard axioms)**: the sketch went through
    link for link, with one correction to the attack log. **Attack (2) was a false alarm**:
    `d ≥ 1` is *not* needed and T018 is *not* used. The feared vacuity cannot arise because
    `H'` is not "whatever is left over" but is *constructed* as `charPowerSeries u₂` of the
    `F`-block, and `H'(a) ≠ 0` comes from Prop. 11 applied to that block, which is valid for
    every `d` (including `d = 0`). The `a ≠ 0` that Q2 needs comes from `h0 0` + T019, not
    from T018. The decisive engineering move, not foreseen in the plan, was to package
    conjugation `T ↦ e ∘ T ∘ e⁻¹` as a **`RingEquiv`** (`conjRingEquiv`): `map_pow` then
    carries the nilpotency of `1 − a·u|_N` to the `Fin d` block and `IsUnit.map` carries the
    invertibility of `1 − a·u|_F` to the `s` block, so no conjugation algebra is written by
    hand. The anticipated "small conj-compactoid lemma" was not needed either:
    `IsCompactoid u₂` follows from Q3's `isCompactoid_of_comp_embedding` applied to `u'`
    along `Function.Embedding.subtype`, exactly as `charPowerSeries_blockTriangular` does
    internally. Two elaboration traps are recorded in the T028 ticket (the `whnf` blow-up
    when `exact` is asked to bridge `conjRingEquiv` under `charPowerSeries`, and the
    `NormedSpace K c(I,K)` module diamond).
- **Q5** (leaf): `finrank_ker_one_sub_smul_pow`
  - Source: [Serre1962, p. 81], verbatim:
    > "D'après la proposition 11, on a H′(a) ≠ 0, et comme a est zéro d'ordre h de
    > H(t), on en déduit finalement que dim N(a) = h, cqfd."
  - Lean ↔ source: from Q4's factorisation `H = ℓ^d · H'`, T006 computes the
    `Δ`-order of `ℓ^d·H'` at `a` to be exactly `d`; Q1 (order uniqueness) against
    the hypothesis order `h` gives `d = h`.
  - Attacks: (1) T006 hypothesis check: needs `H'` entire ✓ (Q4 provides) and
    `a⁻¹·a = 1` ✓. (2) the `hunit`-vs-`≠0` bridge over a field ✓ (`Ne.isUnit`).
    (3) no circularity: Q4 does not use Q5 ✓ (dependency audit done). SURVIVED.
  - **Deviation recorded**: Serre's ≤-half (the supremum over finite-dimensional
    stable `W ⊆ N`) is NOT transcribed — with `N` already finite-dimensional (P4)
    the exact factorisation route replaces it. Quote-or-delete satisfied: the
    quoted passage IS the route we take (his final sentence).
  - **RESOLVED 2026-08-05 (T029, sorry-free, standard axioms)**: exactly the sketch, 16
    lines, no helper. Both attacks held as predicted.
- **Q6** (assembly): `exists_riesz_decomposition`
  - Marked assembly node: instantiates `h` (T019), `N := ker ψ`, `F := range ψ`
    (= `range p` by P2), and assembles P2/P4/Q5/T-outputs; the conjunction is the
    literature statement [Serre1962, Prop. 12]; one-line-per-conjunct from parts.
  - Attacks: composition-shape audit done (each conjunct named to its source
    lemma); the `∀ y ∈ F, ∃ x ∈ F` surjectivity conjunct comes from `w` (`x := w y`,
    `wy ∈ F` by commuting) ✓; injectivity-on-F from P2's range charac. +
    `ψ`-invertibility ✓. SURVIVED.
  - **RESOLVED 2026-08-05 (T030 = MILESTONE-2, sorry-free, standard axioms)**: one line per
    conjunct as planned. The one place the plan wavered (injectivity on `F`) is settled by
    the derived identity `hwb : w * (1 - a•u) = p` — obtained from `hw` by commuting
    `1 - a•u` past `w` — after which `x = p x = w ((1-a•u) x) = w 0 = 0`.
  - Prior-B2 (all Q): no match.

### Confidence gate re-run (extension)

1–7 re-checked for the new leaves: skeleton compiles (0 errors, 67 sorries total);
every new leaf has a verbatim quote (Serre p. 81 / p. 77 / Buzzard p. 23) + match
paragraph + ≥3 attacks (three attacks SUCCEEDED during planning and reshaped
discharges: P3's idempotent-equality gap, P4's `HasPr` cardinality obstruction, Q4's
`d ≥ 1` vacuity — all repaired and recorded); prior-B2 clean; tree mirrors Serre's
p. 81 proof with two recorded deviations (P4's Buzzard-route finiteness; Q5's
factorisation-instead-of-supremum). Gate PASSES.
