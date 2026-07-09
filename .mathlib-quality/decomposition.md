# Decomposition: T038 `isPotentiallyONable_of_uniformizer` (Serre's theorem)

Scope: the `/develop --decompose` pass for the single API-gap ticket T038.  Adversarial
disposition applied per leaf (attacks logged).  Prior-B2 log: `.mathlib-quality/b2_log.jsonl`
created empty at this pass — **no entries, no matches possible** (recorded once here; per-leaf
consultation is vacuous and not repeated below).

## Skeleton location
`PhD/Test/CompactOperatorsMerged.lean` §10 `SerreResidue` (routed to
`PhD/TateFredholm/Residue.lean` by T001).  Declarations `exists_norm_eq_zpow`,
`unitBall`, `unitBall_isUnit_iff`, `isMaximal_span_pi`, `exists_residue_approx`,
`exists_expansion_of_residue_approx`, `expansion_unique_of_residue_indep`,
`isONable_of_discrete_norms`, `rescale`, `le_rescale_and_rescale_lt`, `rescale_add_le`,
`rescale_smul`; assembly target `isPotentiallyONable_of_uniformizer` (§9).
`lake build` passes, 54 sorries total, no type errors — verified 2026-07-09.

## Result: isPotentiallyONable_of_uniformizer

### Source and its proof, located
[Bel] = Bellaïche, Eigenbook draft (scratchpad `Eigenbook.pdf`), §II.1.4, p. 58 (printed):
Hypothesis II.1.11, Lemma II.1.12 (statement + full proof), Theorem II.1.13 (statement +
proof).  Deeper source: [Serre] Publ. IHÉS 12 (1962), Prop. 1.  Every quoted passage
below was extracted from the PDF during this session and is on p. 58 unless noted.

### Plain-English proof (Step 1, mirroring the source)
Let `K` be discretely valued with uniformiser `π` (largest norm < 1; all elements of a
field are multiplicative, so Hypothesis II.1.11 holds).  **(A)** Replace the norm on `E`
by `‖m‖′ = inf {‖π‖^n ≥ ‖m‖}`: an equivalent norm whose nonzero values lie in `‖π‖^ℤ`
([Bel] Thm II.1.13 proof, one line).  **(B)** For a Banach space with norm values in
`‖π‖^ℤ`: the unit ball `E⁰` is a module over the subring `K⁰`, the residue module
`Ẽ = E⁰/πE⁰` is a vector space over the residue field `K̃ = K⁰/(π)` — a field because
`(π)` is exactly the nonunits of `K⁰` (discreteness) — hence `Ẽ` has a basis; lift it to
norm-one vectors `(eᵢ)`.  **(C)** Successive approximation ([Bel] Lemma II.1.12 proof):
every `m ∈ E⁰` is approximated to order `π` by a finite `K⁰`-combination of the `eᵢ`
(residues span); iterating gives coefficient sequences with `|aⁿᵢ − aⁿ⁺¹ᵢ| ≤ |π|ⁿ`, Cauchy,
converging to a `c(ι,K)`-expansion `m = ∑ aᵢeᵢ` with `‖m‖ = supᵢ‖aᵢ‖`; residue
independence gives uniqueness.  The coefficient map is then an isometric isomorphism
`E ≅ c(ι, K)`, i.e. `(E, ‖·‖′)` is ONable; composed with the identity homeomorphism
`(E,‖·‖) ≃L (E,‖·‖′)` this is potential ONability of `E`.

### Leaves

- **R1** (leaf): `exists_norm_eq_zpow` — value group is `‖π‖^ℤ`.
  - Source (verbatim, p. 58): "We choose such an element π.  It is then clear that the
    set of non-zero norms |R∗| is the discrete subgroup |π|Z of the multiplicative group
    of positive real numbers."
  - Lean ↔ source: the Lean statement is the "clear" claim made explicit: every `x ≠ 0`
    has `‖x‖ = ‖π‖^n`.  Proof (expanding the source's "clear"): pick `n` with
    `‖π‖^(n+1) < ‖x‖ ≤ ‖π‖^n` (archimedean property of ℝ, `‖π‖ < 1`); then
    `y = x * π^(-n)` has `‖y‖ ∈ (‖π‖, 1]` (field norm multiplicative, `norm_zpow`);
    if `‖y‖ < 1` then `hπmax` forces `‖y‖ ≤ ‖π‖`, contradiction; so `‖y‖ = 1`.
  - Discharged by: mathlib `norm_zpow`, `norm_mul` (field), `exists_zpow`-style
    archimedean sandwich (compose `Real.exists_int_pow...`-family or hand-roll ≤ 15
    lines from `Real.log` monotonicity — small composition).
  - Attacks: [edge] `x` a unit of norm 1 → `n = 0` ✓; `x = π` → `n = 1` ✓.
    [hypothesis] drop `hπmax`: false for `K = ℂ_p` (value group dense, e.g.
    `‖p^(1/2)‖ ∉ pℤ`) — `hπmax` necessary ✓ not over-specified.  [source-drift]
    statement is exactly the source's parenthetical; no drift.  Verdict: SURVIVED.

- **R2** (leaf): `unitBall` — `{‖x‖ ≤ 1}` is a subring.
  - Source (verbatim, p. 58): "We denote by R0 the set of elements r of R such that
    |r|≤ 1, which is a subring of R".
  - Lean ↔ source: literal.  Discharged by: `norm_mul` (≤ 1·1), ultrametric
    `IsUltrametricDist` add-bound, `norm_one`, `norm_zero`, `norm_neg` — 5 one-line
    fields.
  - Attacks: [edge] trivial? `K` nontrivial field ✓ ball proper (`NontriviallyNormedField`
    has elements of norm > 1) — no degeneracy.  [hypothesis] ultrametric needed for
    `add_mem` (archimedean counterexample: `ℝ`, `x = y = 1`, `‖x+y‖ = 2`) ✓ necessary.
    [discharge] all five cited lemmas standard, `Subring` constructor shape checked at
    skeleton build ✓.  Verdict: SURVIVED.

- **R3** (leaf): `unitBall_isUnit_iff` — units of `K⁰` = norm-one elements.
  - Source: implicit in the source's "|π|Z" discreteness discussion and in [Serre] §1;
    structural note: this is the standard valuation-ring fact making R4 work.  (No
    verbatim sentence in [Bel] — flagged, accepted because R4's maximality claim, which
    [Bel] uses through "M̃ has a basis over 𝔽_p" [quotient by π of ℤ_p is a field],
    requires exactly this; the general-K reformulation is [Serre]'s setting.  Cross-ref:
    any valuation-theory text, e.g. Bosch–Güntzer–Remmert §1.)
  - Lean ↔ source: `IsUnit x ↔ ‖x‖ = 1` inside the subring.  Proof: (⇐) inverse in `K`
    has norm 1 (field: `norm_inv`), lies in ball; (⇒) `1 = ‖x·x⁻¹‖ = ‖x‖‖x⁻¹‖`, both
    `≤ 1` forces both `= 1`.
  - Discharged by: `norm_inv`, `norm_mul`, `Units` constructor + `Subring` coe API.
  - Attacks: [edge] `x = 1` ✓; `x = π` not a unit (norm < 1) ✓ consistent with R4.
    [counterexample-search] over a non-field normed ring the (⇐) fails (no inverse) —
    statement correctly scoped to the field's unit ball ✓.  [discharge] names standard ✓.
    Verdict: SURVIVED.

- **R4** (leaf): `isMaximal_span_pi` — `(π)` maximal in `K⁰`.
  - Source: [Bel] p. 58 uses `R̃ = R⁰/πR⁰` and (Thm II.1.13 proof, verbatim): "Lemma
    II.1.12 show that M is potentially orthonormalizable if and only if ˜M has a basis
    over Fp."  For `R = ℚ_p`, `R̃ = 𝔽_p` *is a field* — our leaf is that statement at
    general discretely-valued `K`.
  - Lean ↔ source: maximality of `(π)` ⟺ `K̃` a field (`Ideal.Quotient.field`), which is
    what "basis over 𝔽_p ⇒ free" consumes.  Proof: by R1 every `x ∈ K⁰ \ (π)` has
    `‖x‖ = 1` (norms in `‖π‖^ℤ`, not ≤ `‖π‖`, so `= ‖π‖^0`); by R3 it is a unit; an
    ideal containing a unit is `⊤` — `Ideal.isMaximal_iff`.  Membership `x ∈ (π) ↔
    ‖x‖ ≤ ‖π‖`: divide by `π` (field), `Ideal.mem_span_singleton`.
  - Discharged by: `Ideal.isMaximal_iff`, `Ideal.mem_span_singleton`, R1, R3.
  - Attacks: [edge] is `(π)` proper? `π` not a unit by R3 (`‖π‖ < 1`) ✓.  [composition]
    children true, parent false? — the R1+R3 route is exhaustive on norms by
    discreteness; no third case ✓.  [hypothesis] without `hπmax`, `(π)` is NOT maximal
    in `𝒪_{ℂ_p}` (nonunits are not principal) — hypothesis necessary ✓.
    Verdict: SURVIVED.

- **R5** (internal): `exists_residue_approx` — norm-one family whose residues form a
  basis, stated quotient-free (spanning = one-step approximation; independence =
  norm-detection).
  - Source (verbatim, p. 58, Lemma II.1.12 proof): "We can write ˜m =∑αi˜ei with the αi
    in ˜R, almost all 0.  Choosing lifts a1i of the αi in R0, we have m−∑a1iei =πm1
    with m1∈M 0."  — that is exactly the spanning clause; the independence clause is the
    "only if" direction's input ("(˜ei)i∈I is a basis").
  - Lean ↔ source: `∃ a : ι →₀ K` finitely supported with unit-ball coefficients and
    `‖m − ∑ aᵢeᵢ‖ ≤ ‖π‖` transcribes "= πm₁ with m₁ ∈ M⁰" (norm ≤ ‖π‖·1); the
    independence clause transcribes "basis": a combination that is ≡ 0 mod π has all
    coefficients ≡ 0 mod π (norms ≤ ‖π‖, using discreteness).  `‖eᵢ‖ = 1` from lifting
    nonzero residues under `hE` (norms in `‖π‖^ℤ`; residue nonzero forces norm `> ‖π‖`,
    hence `= 1`).
  - Sub-decomposition (proof route): (i) `Module K⁰ E` by `Module.compHom` along
    `(unitBall K).subtype`; `E⁰` a `K⁰`-submodule (skeleton keeps these local to the
    proof); (ii) `Ẽ = E⁰ ⧸ (span{π} • ⊤)` a module over `K̃ = K⁰ ⧸ span{π}` — **RISK
    POINT**: the instance `Module (R ⧸ I) (M ⧸ I•⊤)` must be located
    (`Submodule.Quotient.module'`-family) or hand-built via `Module.compHom` +
    well-definedness (≤ 25 lines); (iii) `K̃` is a field: R4 + `Ideal.Quotient.field` ✓
    mathlib; (iv) basis: `Basis.ofVectorSpace` ✓ mathlib (`Module.Free` of vector
    spaces); (v) unfold the quotient statements back to norms (choice of
    representatives, `Submodule.Quotient.mk_eq_mk`-API).
  - Attacks: [edge] `E = 0`: `ι := Empty`-degenerate — statement holds with empty family
    (spanning: `m = 0` handled by `a = 0`, `‖0‖ ≤ ‖π‖` ✓; check `‖m‖ ≤ 1 → ...` at
    `m = 0` ✓).  [hidden-hypothesis] `hE` (discrete norm values) is genuinely used for
    `‖eᵢ‖ = 1` — without it lifts may have norm in `(‖π‖,1)`; hypothesis present ✓.
    [statement-strength] coefficients `ι →₀ K` with `‖aᵢ‖ ≤ 1` rather than `K⁰`-valued:
    equivalent and quotient-free; drift check against source: "αi in R̃, almost all 0.
    Choosing lifts a1i ... in R0" — finite support + unit-ball ✓ faithful.
    [composition] could (i)–(v) hold and R5 fail? The unfolding (v) is where slippage
    could occur — mitigated by phrasing R5's clauses as *exactly* the unfolded forms.
    Verdict: SURVIVED with one flagged instance-risk (ii); fallback documented.

- **R6a** (leaf, the analytic heart): `exists_expansion_of_residue_approx`.
  - Source (verbatim, p. 58): "Applying the same result to m1, we get m−∑a2iei =π2m2
    with m2∈M 0, and by induction m−∑aniei =πnmn with mn∈M0.  By construction, the
    sequence (ani)n∈N satisfies |ani−an+1i|≤|π|n, hence is Cauchy, and therefore
    converges to an element ai∈ R0 for every i∈ I.  One has m =∑aiei.  If |m| = 1, then
    some a1i has norm 1, and so does ai, and thus |m| = supi|ai|."
  - Lean ↔ source: verbatim transcription; the conclusion packages the limit
    coefficients as `a : c(ι,K)` (decay: at stage `n` only finitely many indices are
    touched and increments are `≤ ‖π‖ⁿ`, so `aᵢ → 0` cofinitely — the source's "almost
    all 0" propagated to the limit), `HasSum` (partial sums differ from `m` by `‖π‖ⁿ`),
    and the norm formula (source's last two sentences, plus scaling by `π`-powers via
    `hE` for general `m` — source: "By replacing m by πnm ... we see that the same
    results holds for any m∈M").
  - Discharged by: project T018 toolkit (`summable_of_tendsto_cofinite`), mathlib
    `cauchySeq_tendsto_of_complete`, geometric decay (`pow` bounds), `HasSum` via
    `Filter.Tendsto` on `Finset`-partial sums.  Sizing: source proof = one paragraph
    (~12 lines, p. 58); expect the largest single proof of the subtree (~120 LOC) due to
    coefficient bookkeeping (`Finsupp` unions across stages).
  - Attacks: [hypothesis] completeness of `E` necessary: dense non-closed subspace of
    `c(ℕ,K)` satisfies the approximation hypothesis but has no expansions inside itself
    ✓ hypothesis present.  [edge] `m = 0`: `a = 0` works; `‖m‖ ≤ 1` scaling loop
    terminates ✓; `ι` infinite uncountable fine (all sums are cofinite-indexed).
    [source-drift] the `⨆ᵢ ‖aᵢ‖ = ‖m‖` clause: source proves it first for `|m| = 1`
    then scales — our statement quantifies over all `m` directly; match paragraph
    records the scaling step, no drift.  Verdict: SURVIVED.

- **R6b** (leaf): `expansion_unique_of_residue_indep`.
  - Source: Lemma II.1.12's "if and only if" ("(ei) is an orthonormal basis" includes
    uniqueness of expansions per Definition II.1.5: "there exists a unique sequence").
    Proof route (source leaves it as "The other direction is easy and left to the
    reader."): subtract, suppose `c := a − b ≠ 0`; by decay the sup `‖c‖∞` is attained
    and lies in `‖π‖^ℤ` ; divide by a scalar of that norm (R1) to normalise to
    `sup = 1`; the finitely many indices with `‖cᵢ‖ = 1`... apply `hindep` to a finite
    truncation: tail is `≤ ‖π‖`-small, head combination has norm ≤ ‖π‖ (from
    `HasSum`-difference `= 0`), so all head coefficients `≤ ‖π‖ < 1` — contradiction.
  - Discharged by: R1, T018 (`norm_tsum_le_iSup`), `Finsupp` truncation bookkeeping.
  - Attacks: [edge] `a = b` trivially ✓; `ι` empty ✓.  [counterexample-search] over a
    *dense*-valued field the sup need not be attained and this argument fails — but
    `hE`-discreteness is available through the caller (flag: R6b as stated does NOT
    carry `hE`; the normalisation step uses attainment — **attack succeeded partially**:
    statement corrected? Re-examined: attainment of the sup of `‖cᵢ‖` follows from
    decay alone (cofinitely small + finitely many large values), no discreteness needed;
    the division step needs a scalar of norm *equal* to the sup — that DOES need the
    sup to be a norm value: it is, being `‖cᵢ‖` for some `i` (attained) ✓ no `hE` needed.
    Attack resolved, statement unchanged.]  [discharge] cited project lemmas exist in
    skeleton ✓.  Verdict: SURVIVED (after one resolved attack).

- **R6** (internal, assembly): `isONable_of_discrete_norms`.
  - Composition: R5 gives the family; R6a/R6b give existence/uniqueness of expansions
    with norms; assemble the coefficient map `E → c(ι,K)` — additive + homogeneous
    (uniqueness forces linearity), isometric (norm clause), surjective (T019-style
    inverse: any `a : c(ι,K)` sums by T018), hence `LinearIsometryEquiv`; `IsONable` by
    definition (`⟨range-indexed s, ⟨iso⟩⟩` — reindex as in T014's route or take
    `s := Set.range e` with injectivity from R6b).
  - Attacks: [composition] children true, parent false? — the only gap is linearity of
    the coefficient map, which is *derived* from uniqueness (R6b applied to
    `a + b` vs the expansion of `m + m′`): checked, no gap.  [edge] `E = 0`: ONable via
    empty index ✓ (`c(∅, K) ≅ 0` — degenerate case must be handled in T014-style
    reindexing; noted for the worker).  Verdict: SURVIVED.

- **R7a/R7b/R7c** (leaves): `le_rescale_and_rescale_lt`, `rescale_add_le`, `rescale_smul`.
  - Source (verbatim, p. 58, Thm II.1.13 proof): "Set |m|′ = inf r∈pZ,r≥|m| r.  Then ||′
    is a norm on M which is equivalent to || and satisfies Hypothesis II.1.11."
  - Lean ↔ source: `rescale` is the closed form of that inf (floor of log-ratio; the inf
    over `{‖π‖ⁿ ≥ ‖m‖}` is attained at the largest such `n`, i.e.
    `⌊log‖m‖/log‖π‖⌋` since `log‖π‖ < 0`); R7a = "equivalent" (sandwich with factor
    `‖π‖⁻¹`); R7b + R7c = "is a norm" (ultrametric + exact homogeneity; homogeneity
    needs R1 — the source's "satisfies Hypothesis II.1.11" is our values-in-`‖π‖^ℤ`,
    definitional for `rescale`).
  - Discharged by: `Real.log` monotonicity, `Int.floor` API (`Int.le_floor`,
    `Int.floor_le`), `zpow` order lemmas (`zpow_le_zpow_right_of_le_one`-family — verify
    exact names at work), R1 for R7c.
  - Attacks: [edge] `m = 0` excluded in R7a (`hm`), included in R7b/R7c via the
    `if`-branch (`rescale π 0 = 0`; `max`/`mul` degeneracies check out: R7c at `c = 0`
    or `m = 0` gives `0 = 0` ✓; R7b with `m + n = 0`, `m ≠ 0` gives `0 ≤ max` ✓).
    [strict-vs-weak] R7a upper bound strict (`<`): at the floor, `‖π‖^n < ‖π‖⁻¹‖m‖`
    holds since `‖π‖^(n+1) ... ` — checked with `n = ⌊·⌋` definition: `‖m‖ > ‖π‖^{n+1}`
    ⟺ `n+1 > log‖m‖/log‖π‖` ✓ strict from floor; edge `‖m‖ = ‖π‖^n` exactly: then
    `rescale = ‖m‖` and `‖m‖ < ‖π‖⁻¹‖m‖` ✓ (since `‖π‖ < 1`).  [hypothesis] R7c
    without `hπmax`: false over `ℂ_p` (`‖c‖` not a power ⇒ `rescale(c•m) ≠ ‖c‖·rescale m`
    generically) ✓ necessary, present.  Verdict: SURVIVED.

- **Assembly** (internal): `isPotentiallyONable_of_uniformizer` (§9).
  - Composition: type synonym `E′ := E` with the `rescale`-norm — instances built from
    R7a–c (NormedAddCommGroup via `AddGroupNorm`, NormedSpace from R7c, ultrametric from
    R7b, complete + `E ≃L[K] E′` = identity, continuity both ways from R7a's sandwich);
    `hE′` (values in `‖π‖^ℤ`) is definitional; R6 gives `IsONable K E′`, hence
    `IsPotentiallyONable K E′`→ transport along the identity `≃L` (composition of the
    R6-iso with the identity equiv) gives `IsPotentiallyONable K E`.
  - Source (verbatim): "Then ||′ is a norm on M which is equivalent to || and satisfies
    Hypothesis II.1.11.  Lemma II.1.12 show that M is potentially orthonormalizable if
    and only if ˜M has a basis over Fp.  The result follows."
  - Attacks: [composition] equivalent norm ⇒ same `CompleteSpace`: needs the identity
    to be a bicontinuous equiv, i.e. Lipschitz both ways from R7a — factor `‖π‖⁻¹` both
    directions ✓; instance-diamond risk on the synonym (two `Norm` instances on defeq
    types) — standard type-synonym hygiene (fresh structure via `def E′ := E`,
    instances only on `E′`) ✓ pattern known from `Ix`.  Verdict: SURVIVED.

### Confidence gate (Step 5)
1. Every leaf discharged (mathlib small-compositions or project T018/skeleton) or the
   flagged instance-risk in R5(ii) with a bounded hand-build fallback ✓
2. Skeleton compiles: `lake build` ✓ (54 sorries, 0 errors) ✓
3. Verbatim quotes: R1, R2, R5, R6a, R7, assembly direct from p. 58; R3/R4 carry the
   documented reformulation note (general-`K` form of the source's `𝔽_p` step, backed by
   [Serre]) ✓
4. Adversarial pass: every node has an attack log; one attack partially succeeded (R6b
   normalisation step) and was resolved by re-examination without statement change ✓
5. Prior-B2 log: empty, no matches ✓
6. Tree mirrors the source: R5/R6a/R6b are Lemma II.1.12's proof paragraphs; R7 and the
   assembly are Theorem II.1.13's proof sentences; R1–R4 are the source's setup
   sentences made explicit; sizing anchored to the source's paragraph lengths ✓
7. Single-conclusion check: R5's three clauses are a shared-witness existential (the
   family `e` is the witness for all three) — documented exception per
   statement-splitting rules; R6a's two conclusions share the witness `a` — same
   exception; all other leaves single-conclusion ✓

**Gate: PASS.**  Tickets T039–T046 + assembly T038 created on the board.
