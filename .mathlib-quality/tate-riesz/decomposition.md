# Decomposition for `tate-riesz` (ring-level Riesz theory over the halo Tate ring)

Planned 2026-09-05.  Sources and line locators: `references/{jn,bellaiche,buzzard,lwx}.txt`
(pypdf extracts; `===== PDF PAGE n =====` markers).  Quotes below are verbatim from those
extracts (extraction garbling of symbols is cosmetic).

## Skeleton location

Every lemma of the tree is stated with `:= by sorry` in:
- `PhD/TateFredholm/Entire.lean` (242 lines, 28 sorries)
- `PhD/TateFredholm/Resultant.lean` (48, 2)
- `PhD/TateFredholm/Coleman.lean` (286, 26)
- `PhD/TateFredholm/RieszColeman.lean` (292, 22)
- `PhD/TateFredholm/SlopeFactor.lean` (107, 5)
- `PhD/LWX/HaloTate.lean` (233, 43 — instance/structure proof fields included)
- `PhD/LWX/TateRiesz.lean` (161, 12; `UpDatum.tateOp` is a *data* sorry, filled by F1)

`lake build PhD.LWX.TateRiesz PhD.TateFredholm.RieszColeman PhD.TateFredholm.SlopeFactor
PhD.TateFredholm.Coleman PhD.TateFredholm.Resultant PhD.TateFredholm.Entire PhD.LWX.HaloTate`:
**Build completed successfully (2898 jobs)**, sorries only, no type errors — verified
2026-09-05 11:10.

Statement-shape check (gate 7): every leaf is single-conclusion except the documented
shared-witness existentials (`exists_rieszColemanProjection`, `exists_rieszProjection_isOpLimit`,
`exists_isDominantFactorization`, `exists_rieszColemanProjection_tateOp`, `IsGoodZero.exists_factor`,
`IsEntire.exists_eq_mul_add`), which follow `Riesz.lean`'s `exists_rieszProjection` pattern
(bundle + per-property spec lemmas taking the defining properties as hypotheses:
`IsRieszColemanProjection.*`), and the two `Prop`-structures `IsRieszColemanProjection`,
`IsDominantFactorization` (each field is one conclusion; consumers project).

## Prior-B2 log consultation (Step 4.6)

Logs read: `.mathlib-quality/b2_log.jsonl` (3 entries: `NewtonPolygon₀.unitSlope_cases`,
`NewtonPolygon₀.lengths_final`, `LWX.exists_binomial_basis`) and
`.mathlib-quality/lwx-halo/b2_log.jsonl` (3 entries: `LWX.cfunSlash_mahlerEmbed`,
`LWX.mahlerEmbed_seqSlash`, `LWX.seqSlash_coeff`).

- **No name match** with any leaf of this tree.
- **Shape match, addressed:** the three `lwx-halo` entries record that "the `T`-rescaled
  transport forces `b m = Δ̃^m F 0 / T^m`, which is not `c₀`" — i.e. the rescaled Mahler
  coordinates are not `c₀`-stable under the action.  Tranche F's operator over `A` is therefore
  **not** the rescaled `U_p` on `c₀`-coordinates but its **transpose** `V = (D⁻¹PD)ᵀ`, whose
  entries at row `(j,n)` are bounded by `p^{−(n−⌊n/p⌋)}` uniformly in the column (L-F2/L-F3
  below, verified by hand: `‖T^{n−m}M_{(i,m),(j,n)}‖ ≤ p^{−(n−m)−max(m−⌊n/p⌋,0)} ≤ p^{−(n−⌊n/p⌋)}`
  in both cases `m ≤ ⌊n/p⌋`, `m > ⌊n/p⌋`), so `V` is compactoid and its columns are in `c₀`.
- **Shape match, addressed:** `LWX.exists_binomial_basis` failed for `ρ > 1` and in
  characteristic `p` (the planner overshot the source's `ρ = p^{−s} ≤ 1`, `ℤ_p`-coefficients).
  Every radius-parametrised leaf here (`IsDominantIndex ρ`, `norm_coeff_dPoly_le_pow`) is
  stated with explicit `0 < ρ` / `1 ≤ C` hypotheses only where the source uses them, and the
  Coleman estimates are proved by the unit-rescaling trick, valid for every radius; no
  characteristic assumption enters (Banach–Tate rings of characteristic `p` are in scope, as in
  [JN]).
- The `NewtonPolygon` entries concern the polygon API, not consumed here.

Verdict: clean of unaddressed prior B2 history.

---

## Result T1 — the Banach–Tate ring `A = HaloInt[1/T]` (`PhD/LWX/HaloTate.lean`)

### Plain-English proof (source structure)
[JN] Definition 2.1.2 (jn.txt 483–490, p. 7): a normed ring is Tate if it contains a
multiplicative unit `ϖ` with `|ϖ| < 1`; complete ⇒ Banach–Tate.  [JN] Remark 2.1.3(1)
(jn.txt 495–500, p. 8): "the unit ball `R₀` is a ring of definition and `ϖ` is a topologically
nilpotent unit".  The `lwx-halo` plan describes `A` as `Λ^{>1/p}[1/T]` with `T` inverted
(HaloRing.lean's docstring: "`T` acts as a pseudo-uniformizer would, without being a unit").
Concretely `A = ⋃_k T^{−k}·HaloInt p`, i.e. streams with `‖d j‖ ≤ p^{min(0, j+k)}`; the gauge
norm of HaloRing.lean extends verbatim; `T` is a unit with `‖T·x‖ = p⁻¹‖x‖`, so `T` is a
multiplicative pseudo-uniformizer.  Every proof is the `HaloInt` proof with shifted bounds
(the convolution's tails still die: `‖f_i g_{k−i}‖ ≤ p^{min(0,i+k₁)+min(0,k−i+k₂)}`).

### Lemmas
- **L-A1** (leaf, project): `HaloTate` carrier, `summable_mul_coeff`, ring instances, `coeff_*`,
  `ofIntRingHom`, `ofInt_injective`, `norm_coeff_le_one` — HaloTate.lean:34–124.
  - Source: HaloRing.lean's construction (lines 44–262, 218 lines) mirrored; [LWX] Lemma 3.15
    (lwx.txt 1591–1595): "Λ^{>1/p} := ΛJpT^{−1}K = Z_pJT,pT^{−1}K ⊗ Z_p[∆] … The ideal m_ΛΛ^{>1/p}
    is the same as the principal ideal (T)."  [LWX] Cor 3.18 proof (lwx.txt 1689–1690): "if
    ∑_{m∈Z} d_mT^m ∈ Λ^{>1/p}, then v(d_m) ≥ max{0,−m}."
  - Lean ↔ source: `exists_bound'` is "`T^k d ∈ Λ^{>1/p}`" unpacked coefficientwise, exactly
    the Cor 3.18 description shifted by `k`.
  - Discharged by: `HaloRing.lean` proofs (`tendsto_cofinite_of_three_bounds` to be
    un-privated — same lemma with `a = i+k₁`, `b = k−i+k₂`, `c = 0`), `TateFredholm.summable_of_tendsto_cofinite`,
    `Summable.tsum_prod'`, `Equiv.subLeft` (all verified in HaloRing.lean).
  - Sizing: HaloRing's A1 ticket was ~220 LOC; expect ~250 LOC.
  - Attacks: [1] counterexample: none — `A` is a ring by transport of the same convolution
    identities; [2] edge cases: `k = 0` recovers `HaloInt` (`ofInt`); `f = 0`; `f = T⁻¹` (bound
    `k = 1`) ✓; [3] hypotheses: no `p ≠ 2` needed (none in HaloRing either); [4] source drift:
    `A` is the localisation, not the completion — matches "`[1/T]`" in the lwx-halo proposal and
    [JN]'s "ring of definition `R₀`" picture (the unit ball is `HaloInt`, L-A2); [5] discharge:
    `tendsto_cofinite_of_three_bounds` has the needed `min 0 · + min 0 · + min 0 ·` shape (read at
    HaloRing.lean:74–96). SURVIVED.
- **L-A2** (leaf, project): gauge norm, `NormedRing`, `NormOneClass`, `IsUltrametricDist`,
  `CompleteSpace`, `norm_ofInt`, `norm_le_one_iff` — HaloTate.lean:128–174.
  - Source: HaloRing.lean:265–440 (norm section, ~175 lines) mirrored; [JN] Rmk 2.1.3(1)
    (jn.txt 495–497): "The underlying topological ring is a Tate ring in the language of Huber;
    the unit ball R₀ is a ring of definition".
  - Lean ↔ source: `norm_le_one_iff` is "unit ball = `HaloInt`".
  - Discharged by: `gnorm_*` proofs of HaloRing (the sup is finite by `exists_bound`), `HaloInt.norm_def`.
  - Attacks: [1] is the sup finite? yes: `‖f j‖p^{−j} ≤ p^{min(0,j+k)−j} ≤ p^{k}`; [2] edge: `f = T⁻¹`:
    `‖T⁻¹‖ = p` ✓ consistent with `norm_T_mul`; [3] completeness needs a uniform `k` along a
    Cauchy sequence — true: a Cauchy sequence is bounded, `‖f‖ ≤ p^K` gives `k = K` uniformly
    (recorded in the ticket sketch); [4] drift: none; [5] discharge: mirror. SURVIVED.
- **L-A3** (leaf, project/mathlib): `T`, `coeff_T_mul`, `norm_T_mul`, `norm_T`, `norm_T_lt_one`,
  `pseudoUniformizer`, `instance IsTate`, `exists_T_zpow_mul_ofInt`,
  `isMultiplicative_ofInt_of_isUnit`, `isMultiplicative_mul` — HaloTate.lean:176–228.
  - Source: [JN] Def 2.1.2 (jn.txt 483–486): "We say that R is Tate if R contains a
    multiplicative unit ϖ such that |ϖ| < 1. We call such a ϖ a multiplicative
    pseudo-uniformizer. If R is also complete, we say that R is a Banach–Tate ring."; [JN] p. 8
    (jn.txt 493–494): "a unit ϖ in a normed ring R is multiplicative if and only if |ϖ^{−1}| = |ϖ|^{−1}";
    HaloRing.lean `norm_T_mul` (lines 473–495) for the shift computation.
  - Lean ↔ source: `pseudoUniformizer` packs `T`, `‖T‖ = p⁻¹ < 1`, `‖Tx‖ = ‖T‖‖x‖` — Def 2.1.2 verbatim.
  - Discharged by: `TateFredholm.PseudoUniformizer` (Tate.lean:182), `IsTate` (215); norm-1 units
    multiplicative: `‖ux‖ ≤ ‖x‖ = ‖u⁻¹ux‖ ≤ ‖ux‖`.
  - Attacks: [1] none; [2] edge: `x = 0`; `p = 2` (nothing breaks: no `p ≠ 2` here); [3] `‖e‖ = 1`
    alone does NOT give multiplicativity for a non-unit — the lemma requires `e` a unit of
    `HaloInt` (so `‖e⁻¹‖ ≤ 1` too) ✓ hypothesis necessary; [4] drift: none; [5] `IsTate` is a
    `Prop` class with a `Nonempty` field (Tate.lean:215) ✓. SURVIVED.

## Result T2 — entire series (`PhD/TateFredholm/Entire.lean`)

### Plain-English proof (source structure)
[Bel] Def II.1.16 (bellaiche.txt 2155–2158, p. 59) defines `R{{T}}`; [JN] §2.1 (jn.txt 498–500,
p. 9) "det(1−Tu) ∈ R{{T}}, where R{{T}} = {∑ a_nT^n ∈ R[[T]] | |a_m|M^m → 0 ∀M ∈ R≥0}".  [Bel]
Prop II.2.8 (bellaiche.txt 2380–2445, pp. 66–67, ~65 lines incl. proof) is Euclidean division;
its proof reduces to monic `B`, proves uniqueness by a dominant-term argument and existence by
the polynomial estimate (II.2.1) and a limit.  We discharge it from Martin's Weierstrass division
(already formalised) at a radius where `B` is distinguished.  Cor II.2.9 (bellaiche.txt 2446–2448)
is `R[T]/(B) ≅ R{{T}}/(B)`.  [JN] Def 2.2.1 (jn.txt 660–666) defines Fredholm series, multiplicative
polynomials and relative primality.  [Bel] Def II.2.11 (bellaiche.txt 2470–2473), Ex II.2.12 and
the paragraph after (2474–2480) define good zeros and factor `(1−a^{−1}T)^s`.  [Buz07] p. 22
(buzzard.txt 786–800) gives the Leibniz rule for `Δ_s`.

### Lemmas
- **L-B1** (leaf, mathlib+project): `IsEntire`, `isEntire_iff`, `IsEntire.tendsto_norm_coeff_mul_pow`,
  `isEntire_C/one/X`, `IsEntire.add/neg/sub/mul/pow/hasseDeriv`, `Polynomial.isEntire_coe`,
  `entireSubring`, `IsEntire.evalT_mul/add`, `hasseDeriv_mul` — Entire.lean:42–127.
  - Source: [Bel] Def II.1.16: "We denote by R{{T}} the ring of power series ∑_{n=0}^∞ a_nT^n
    with a_n ∈ R that converge everywhere, in the sense that |a_n|C^n → 0 for every positive real
    C."  [Buz07] p. 22: "If f,g ∈ A[[T]] then it is possible to check that ∆_s(fg) =
    ∑_{i=0}^s ∆_i(f)∆_{s−i}(g). One also easily checks that … ∆_s sends A{{T}} to itself."
  - Lean ↔ source: `IsEntire f := ∀ c > 0, IsRestricted c f` and `isRestricted_iff'` is exactly
    `‖a_n‖c^n → 0`; the ring closure is [Bel]'s "ring".
  - Discharged by: `PowerSeries.isRestricted_iff'`, `isRestricted.add/neg/mul/pow`,
    `isRestricted_C/X/one` (Restricted/Basic.lean, verified), `tendsto_norm_coeff_mul_pow_of_isRestricted`
    (Riesz.lean:133), `evalT_add/mul` (Riesz.lean:153/211), `isRestricted_hasseDeriv` (Riesz.lean:237,
    private — to un-private or re-prove), `Polynomial.hasseDeriv_mul` (mathlib pattern) with
    `Nat.add_choose_add`-style Vandermonde for `PowerSeries.hasseDeriv`.
  - Sizing: source is definitional (≤ 10 lines); Leibniz ~40 LOC; expect ~150 LOC total.
  - Attacks: [1] loogle `¬ IsRestricted _ (_ * _)` — no contradiction; `isRestricted.mul` needs
    `[IsUltrametricDist R]` ✓ carried; [2] edges: `c → ∞` (entire ⇒ stronger than restricted at any
    radius), `f = 0`, `k = 0` in Leibniz (`hasseDeriv_zero`) ✓; [3] `hasseDeriv_mul` needs
    commutativity? the sum formula holds over any commutative semiring; stated with `CommSemiring`
    — matches `PowerSeries.hasseDeriv`'s `Semiring` def; [4] drift: none; [5] discharge lemma names
    read in Restricted/Basic.lean:55–105 and Riesz.lean:79–160. SURVIVED.
- **L-B2** (leaf, project): `IsEntire.exists_eq_mul_add`, `eq_mul_add_q_unique`, `eq_mul_add_r_unique`
  — Entire.lean:149–168.
  - Source: [Bel] Prop II.2.8 (verbatim): "Let F ∈ R{{T}} and let B ∈ R[T] a non-zero polynomial
    whose dominant term is invertible in R. Then there exists a unique Q ∈ R{{T}} and S ∈ R[T]
    with deg S < deg B such that F = BQ + S."  Proof (bellaiche.txt 2386–2389): "it is enough to
    prove the proposition when B is monic. Indeed, … let b ∈ R^* be the dominant term of B, so
    that B = bB_0 with B_0 monic."
  - Lean ↔ source: identical statement (the estimates of II.2.8 are L-E1's business).
  - Discharged by: `Polynomial.isMulDistinguished_toRestricted_of_monic` (MulDistinguished.lean:239)
    at a radius `c ≥ max(1, max_i ‖b_i‖)`, `weierstrassDivision_exists_of_isMulDistinguished`
    (MulWeierstrassDivision.lean:343), `weierstrassDivision_q_unique/…_r_unique_of_isMulDistinguished`
    (:96/:110), `isRestricted_of_le` for uniqueness across radii — the pattern of
    `exists_factor_of_evalT_eq_zero` (Riesz.lean:439–447, read).
  - Sizing: source 65 lines; Lean reuses Martin ⇒ ~120 LOC.
  - Attacks: [1] a monic `B` is distinguished at radius `c` only if `‖toRestricted c B‖ = c^s`,
    i.e. `‖b_i‖c^i ≤ c^s` ∀ i < s — true for `c ≥ max(1, ‖b_i‖)` ✓; [2] edges: `B` constant (unit):
    `q = B⁻¹F`, `r = 0` ✓; `F = 0` ✓; [3] hypothesis `IsUnit B.leadingCoeff` necessary
    ([Bel] "dominant term invertible"); no `NormOneClass` needed beyond what `isMulDistinguished_…_of_monic`
    requires (it has `[NormOneClass A]`) ✓ carried; [4] drift: [Bel] states uniqueness with `Q`
    entire — our `q_unique` assumes both quotients entire ✓ same; [5] Martin's division is at a
    fixed radius; entireness of `q` needs the cross-radius uniqueness argument (in the sketch) ✓.
    SURVIVED.
- **L-B3** (leaf, project/mathlib): `IsEntireCoprime`, `.symm`, `.mul_right`,
  `isEntireCoprime_iff_isCoprime_of_eq_mul_add`, `isCoprime_of_mul_add_eq_one` — Entire.lean:171–200.
  - Source: [JN] Def 2.2.1: "Two entire series P,Q ∈ R{{T}} are said to be relatively prime if the
    ideal (P,Q) = R{{T}}."  [Bel] Cor II.2.9: "The natural morphism of R-algebras R[T]/(B(T)) →
    R{{T}}/(B(T)) is an isomorphism."
  - Lean ↔ source: `IsEntireCoprime F G := ∃ a b entire, aF + bG = 1` is "(F,G) = R{{T}}"; the `iff`
    is II.2.9 in the only form consumed (units of `R{{T}}/(B)` are units of `R[T]/(B)`).
  - Discharged by: L-B2 (division of the Bézout coefficient `b` and of `b₂ r` by `B`, uniqueness of
    the division of `1`), `IsCoprime` API (mathlib), `Polynomial.coe_mul/coe_add`.
  - Attacks: [1] `mul_right`: `(F, G) = 1 ∧ (F, G') = 1 ⇒ (F, GG') = 1` — standard
    (`IsCoprime.mul_right` pattern) ✓; [2] edge `B` constant unit: both sides true ✓; `r = 0`: LHS
    false (`(B, Bq) ≠ 1` unless `B` unit) and `IsCoprime B 0 ↔ IsUnit B` ✓ consistent; [3] the `(⇒)`
    direction genuinely needs uniqueness of Euclidean division (L-B2) — no hidden assumption;
    [4] drift: none; [5] discharge chain checked step by step in the ticket sketch. SURVIVED.
- **L-B4** (leaf, project): `IsGoodZero`, `.isUnit`, `.mul`, `.of_mul`, `.exists_factor`,
  `IsEntire.eq_zero_of_forall_evalT_pow_eq_zero` — Entire.lean:133–140, 210–239.
  - Source: [Bel] Def II.2.11: "We say that a is a good zero of order s of F if F^{(0)}(a) =
    F^{(1)}(a) = ··· = F^{(s−1)}(a) = 0 and F^{(s)}(a) is a unit in R."  Ex II.2.12: "If F(0) = 1 and
    F(a) = 0, then a is a unit in R."  §II.2.3: "If a is a good zero of F of order s ≥ 1, we can
    write F(T) = (1−a^{−1}T)G_1(T) with G_1(T) ∈ R{{T}} by Prop. II.2.8 and we see that a is a
    good zero of G_1 of order s−1. By induction, we can write F = (1−a^{−1}T)^sG(T) with
    G(T) ∈ R{{T}} and G(a) a unit in R."  Identity theorem: expansion of [Buz07] p. 20's
    unproved "det(1 − X(φ ⊕ ψ)) = det(1 − Xφ) det(1 − Xψ)" (used in L-D3).
  - Lean ↔ source: `IsGoodZero F a s` is Def II.2.11 with `evalT a (hasseDeriv i F)` for
    `F^{(i)}(a)` (Bellaïche's `F^{(i)}` are the divided derivatives, cf. [Buz07] p. 22 `Δ_s`);
    `exists_factor` is §II.2.3 with the unit `u = a` explicit.
  - Discharged by: L-B1 Leibniz + `IsEntire.evalT_mul`, L-B2 division by `1 − u⁻¹X` (unit
    leading coefficient), `evalT_hasseDeriv_pow_mul_of_lt` (Riesz.lean:330, pattern); identity
    theorem: ultrametric bound on the lowest nonzero coefficient with `a = ϖ^k → 0`.
  - Attacks: [1] `.of_mul` fails without `G(a)` a unit (e.g. `G = 1 − a⁻¹T` raises the order)
    — hypothesis present ✓; [2] edges: `s = 0` (`IsGoodZero F a 0 ↔ IsUnit (F(a))`, `exists_factor`
    gives `G = F`) ✓; `a = 0`: `F(0) = 1` so `0` is not a good zero of order ≥ 1 ✓ (`.isUnit` needs
    `1 ≤ s` ✓ present); identity theorem with `R` trivial: `[Nontrivial R]` assumed (needed for
    `ϖ`'s norm to be positive) ✓; [3] `.isUnit` uses `coeff 0 F = 1` (Ex II.2.12's `F(0) = 1`) ✓;
    [4] drift: none; [5] discharges read. SURVIVED.

## Result T3 — `Res(charpoly A, g) = det g(A)` (`PhD/TateFredholm/Resultant.lean`)

### Plain-English proof (source structure)
[Bel] Prop II.2.16's proof (bellaiche.txt 2543–2554): "we shall prove it for any commutative ring
R. Actually, standard argument shows that is its enough to prove it when R is an algebraic closed
field K. In this case, we can write det(1−Tφ) = (1−a_1T)…(1−a_nT) with a_1,…,a_n ∈ K^* being the
eigenvalues of φ … By definition of D, one has D(Q, det(1−Tφ)) = (1−Q(a_1))…(1−Q(a_n)) which is
just det(1−TQ(φ))."  With `D` defined as a resultant, the identity to prove is
`Res(charpoly A, g) = det g(A)`; the "standard argument" is the universal characteristic
polynomial.

### Lemmas
- **L-R1** (leaf, mathlib): `Matrix.det_aeval_eq_prod_roots` — Resultant.lean:36.
  - Source: as above ("det(1−TQ(φ)) = ∏(1 − Q(a_i))" over an algebraically closed field).
  - Lean ↔ source: for `g` and `charpoly A` split over a domain, `det g(A) = ∏_{λ ∈ roots} g(λ)`;
    at `g = 1 − TB` this is Bellaïche's display.
  - Discharged by: `Polynomial.Splits.eq_prod_roots` (Splits.lean:299), `Polynomial.aeval` is a
    ring hom (`map_mul`, `map_prod`), `Matrix.det_mul`, `Matrix.eval_charpoly` (Charpoly/Basic:135:
    `M.charpoly.eval t = (scalar t − M).det`), `Matrix.det_neg`, `Finset.prod_comm` — ≤ 3 lemma
    composition per step.
  - Attacks: [1] `g = 0`: LHS `det 0 = 0`, RHS `∏ 0 = 0` (if `n ≠ 0`); for `n = 0` both `1` ✓;
    [2] edge `g` constant `c`: `det(c·1) = c^n = ∏ c` ✓; `A = 0`: roots all `0`, `det g(0) = g(0)^n` ✓;
    [3] `IsDomain` needed for `Splits.eq_prod_roots`/`roots` to behave — present; [4] drift: none;
    [5] `resultant_eq_prod_eval` (Resultant/Basic:479) has `[IsDomain R]`, `f.Splits`, `hg :
    g.natDegree ≤ n` ✓ same shape. SURVIVED.
- **L-R2** (leaf, mathlib): `Matrix.resultant_charpoly` — Resultant.lean:43.
  - Source: [Bel] "standard argument shows that it is enough to prove it when R is an
    algebraically closed field"; [Bel] Lemma II.2.13 proof (bellaiche.txt 2508–2513): "if f : R → R'
    is a morphism of rings, then D(f(B),f(P)) = f(D(B,P)). Clearly it is enough to prove them for a
    ring of polynomials R = Z[x_1,…,x_m] with sufficiently many variables. This ring R is a domain
    and it is enough to prove equations … for an algebraically closed field K containing R."
  - Lean ↔ source: the universal reduction, with `Matrix.charpoly.univ` for the matrix entries and
    `MvPolynomial` variables for `g`'s coefficients.
  - Discharged by: `Matrix.charpoly.univ`, `univ_map_eval₂Hom` (Charpoly/Univ.lean:57),
    `Polynomial.resultant_map_map` (Resultant/Basic:140), `RingHom.map_det`, `Polynomial.aeval_map`-type
    lemmas, `IsAlgClosed.splits` on `AlgebraicClosure (FractionRing S)`, `resultant_eq_prod_eval`
    (Resultant/Basic:479), L-R1, injectivity `S → AlgebraicClosure (FractionRing S)` for
    `S = MvPolynomial _ ℤ` (a domain).
  - Sizing: source 6 lines of "standard argument"; expect ~250 LOC (universal bookkeeping).
  - Attacks: [1] degree parameter: `resultant f g (card n) m` with `f = charpoly A` of natDegree
    `card n` (nontrivial `R`; trivial `R` gives `0 = 0`) ✓; [2] edge `n` empty: `charpoly = 1`,
    `Res(1, g)(0, m) = 1^? …` mathlib `resultant_C_zero_left`-type gives `1` and `det g(A) = 1` ✓;
    [3] no hidden assumption: works over any `CommRing`; [4] drift: none; [5] `resultant_map_map`
    exists (`lemma resultant_map_map (φ : R →+* S)`), `univ_map_eval₂Hom` gives
    `(univ R n).map (eval₂Hom f M) = charpoly (of M.curry)` ✓. SURVIVED.

## Result T4 — Coleman's `D` and the spectral mapping (`PhD/TateFredholm/Coleman.lean`)

### Plain-English proof (source structure)
[Bel] §II.2.4 (bellaiche.txt 2485–2554, pp. 68–69, ~70 lines): define `D(B,P)` for polynomial
`P` with `P(0) = 1` via symmetric functions; Lemma II.2.13 (i)–(iii) by the universal-ring /
algebraically-closed-field reduction; extend to `R{{T}}` by continuity ("the coefficients of
`D(B,P)` are polynomials in the coefficients `a_i` of `P`"), obtaining Lemma II.2.14 by
passage to the limit; Prop II.2.15 (good zero of order `n` at `1`); Prop II.2.16 (spectral
mapping) "reduced as usual to the case where M is orthonormalizable, and then to the case
where φ is of finite rank".  [Buz07] p. 21 (buzzard.txt 738–760) gives the resultant form
`D(B,P) = Res(P*(X), 1 − TB(X))`, the renormalisation trick and `D(uB,P)(T) = D(B,P)(uT)`.
Here `D` is *defined* by the resultant (so (i)–(iii) are mathlib resultant identities), and the
continuity/entireness is made quantitative (multilinearity of the Sylvester determinant +
Buzzard's renormalisation); Prop II.2.15's proof is rearranged to avoid `D(B, A)` for the Bézout
coefficient `A` (which has no constant term `1`): the unit criterion `D(1−Q̃*, S)(1) ∈ R^× ⟺
(Q,S) = R{{T}}` is proved via Euclidean division and mathlib's `isUnit_resultant_iff_isCoprime`.

### Lemmas
- **L-C1** (leaf, mathlib): `gPoly`, `dPoly`, `bQ`, `bQ_coeff_zero`, `natDegree_bQ`,
  `dPoly_coeff_zero`, `dPoly_succ`, `dPoly_mul` — Coleman.lean:46–86.
  - Source: [Buz07] p. 21: "if P has degree n and we define P*(X) = X^nP(X^{−1}), then D(B,P) =
    Res(P*(X), 1 − TB(X))"; [Bel] Lemma II.2.13 (i): "D(B,PQ) = D(B,P)D(B,Q)" [the extract's
    "D(P,Q)" is a typo for D(B,Q), as (ii)/(iii) and the proof "the set of roots of P*Q* = (PQ)*
    … is the union" show]; [Bel] proof of II.2.18: "φ' = 1 − Q*(φ)/Q*(0)".
  - Lean ↔ source: `dPoly B P N = Res_X(reflect N P, 1 − T·B(X))` with degree parameters `N`,
    `deg B`; `reflect N P` is `P*` at degree `N` (Bellaïche's `P*` for `deg P = n`; padding by
    `X^{N−n}` is harmless when `B(0) = 0`: `dPoly_succ`); `bQ Q u = 1 − u⁻¹Q*` is Bellaïche's
    `1 − Q*(φ)/Q*(0)` as a polynomial (`Q*(0) = leadingCoeff Q = u`).
  - Discharged by: `Polynomial.reflect_mul` (Reverse.lean:177), `resultant_mul_left`
    (Resultant/Basic:582, natDegree-parametrised — needs `natDegree (reflect N P) = N`, true
    for `IsUnit (P.coeff 0)` in a nontrivial ring), `resultant_X_pow_left` (:681, gives `Res(X,g) =
    g(0) = 1`), `resultant_add_right_deg` (:343) for `dPoly_coeff_zero`, `coeff_zero_reverse`,
    `reverse_leadingCoeff`.
  - Sizing: source ≤ 15 lines; expect ~200 LOC (degree-parameter bookkeeping).
  - Attacks: [1] `dPoly_mul` with the natDegree-based `resultant_mul_left`: the parameter of
    `reflect (N+M) (PQ)` is `N+M` and `natDegree = N+M` iff `(PQ).coeff 0 = P₀Q₀` is a unit ✓
    (hypotheses `hP0 hQ0`); [2] edges: `B = 0` (`gPoly = 1`, `dPoly = 1^N`…: `resultant f 1 N 0 = 1`
    up to `f.coeff N` powers — `dPoly_coeff_zero` handles; `dPoly_succ` with `B = 0`: `B.coeff 0 = 0`
    ✓ fine); `N = 0`, `P = 1`: `dPoly B 1 0 = Res(1, g)(0, d) = 1` ✓; trivial ring ✓;
    [3] `dPoly_succ` genuinely needs `B(0) = 0` (else `Res(X, 1 − TB)` = `1 − TB(0) ≠ 1`) ✓ present;
    [4] drift: Bellaïche's `D` is defined by symmetric functions; ours by the resultant — [Buz07]
    p. 21 asserts they agree ("In fact … D(B,P) = Res(P*(X), 1 − TB(X))"), and mathlib's
    `resultant_eq_prod_eval` gives `∏(1 − TB(t_i))` over the roots of `reflect N P` ✓ same object;
    [5] all cited lemma names read in Resultant/Basic.lean and Reverse.lean this session.
    SURVIVED.
- **L-C2** (leaf, mathlib): `dPoly_bQ_self`, `eval_one_dPoly_bQ`, `eval_one_dPoly_bQ_add_mul`,
  `isCoprime_reflect_reverse_iff`, `isUnit_eval_one_dPoly_bQ_iff`, `Matrix.charpolyRev_aeval`
  — Coleman.lean:88–130.
  - Source: [Bel] Lemma II.2.13 (ii) "D(1−P*,P)(T) = (1−T)^n", proof "D(1−P*,P)(T) =
    ∏(1−T(1−P*(t_i))) = (1−T)^n"; (iii) "D(1−P*,Q+CP)(1) = D(1−P*,Q)(1)" ("We leave (iii) as an
    exercise"); [Col97, Lemma A3.7] via [JN] Lemma 2.2.7's proof (jn.txt 730–732): "By [Col97,
    Lemma A3.7] it suffices to prove that Res(Q,S) is a unit in R{{T}}"; [Bel] Prop II.2.16
    (finite case) as quoted under T3.
  - Lean ↔ source: (ii) at `T`: `Res(Q*, (1−T) + (T/u)Q*) = Res(Q*, 1−T) = (1−T)^{deg Q}`;
    (iii) at `T = 1`: `Res(reflect_N(P + C'Q), u⁻¹Q*) = Res(reflect_N P + (u·reflect C')·Q*, u⁻¹Q*)`;
    the unit criterion is Coleman's A3.7 in mathlib's polynomial form (`Q*` monic); the finite
    spectral mapping is II.2.16's finite-rank case with `reverse_charpoly`.
  - Discharged by: `resultant_add_mul_right` (:237, "Res(f, g + fp) = Res(f, g) if deg f + deg p ≤
    deg g"), `resultant_add_right_deg`/`resultant_C_zero_right` for `Res(Q*, C(1−T))`,
    `resultant_map_map` along `Polynomial.evalRingHom 1`, `resultant_add_mul_left` (:254),
    `reflect_mul`, `resultant_C_mul_right` (:261), `resultant_comm` (:152),
    `isUnit_resultant_iff_isCoprime` (:886, first argument monic — `Q.reverse` is monic since
    `Q.coeff 0 = 1`: `reverse_leadingCoeff` = `trailingCoeff = coeff 0`), reflection of Bézout
    identities (`reflect_mul`, `reflect_C`, `reflect_one`, `IsCoprime` with `X^M` and `(X, Q)`
    coprime because `Q(0) = 1`), `Matrix.reverse_charpoly` (Charpoly/Coeff:298), L-R2.
  - Sizing: source ~10 lines; expect ~300 LOC.
  - Attacks: [1] (iii) exact or up to units? Recomputed: `resultant_add_mul_left` gives exact
    equality with parameters `(N, deg Q)` provided `deg(u·reflect_{N−n}C') + n ≤ N` ✓ hypothesis
    `hC` present; [2] edges: `C' = 0` trivial; `P = 0`: `reflect 0 = 0`, `Res(0, Q*) = 0^…` and
    `IsCoprime 0 Q ↔ IsUnit Q` — with `Q(0) = 1`, `Q` a unit iff `deg Q = 0`; then `Res` over
    `N ≥ 1`… `resultant_zero_left : Res 0 g m n = 0^n * g.coeff 0^m`: `0^{deg Q}` is `1` iff
    `deg Q = 0` ✓ consistent; [3] `isCoprime_reflect_reverse_iff` needs `Q.coeff 0 = 1` (for
    `(X, Q) = 1`) and `IsUnit Q.leadingCoeff` (for `(X, Q*) = 1`) — both present and necessary
    (`Q = X` with `P = 1`: `reflect_N 1 = X^N`, `Q* = 1`… `Q(0)=0` excluded ✓); [4] drift: none —
    `charpolyRev_aeval`'s `B(0) = 0` is [Bel] II.2.16's "Q(0) = 0"; [5] `isUnit_resultant_iff_isCoprime
    {f g} (hf : f.Monic) : IsUnit (resultant f g) ↔ IsCoprime f g` read at :886 ✓, monic first
    argument ⇒ `resultant_comm` sign flip needed ✓ noted. SURVIVED.
- **L-C3** (leaf, project/mathlib): `norm_coeff_dPoly_le`, `norm_coeff_dPoly_sub_le`,
  `dPoly_comp_C_mul_X`, `dPoly_C_mul`, `norm_coeff_dPoly_le_pow` — Coleman.lean:141–180.
  - Source: [Bel] p. 68: "For B fixed, the coefficients of D(B,P) are polynomials in the
    coefficients a_i of P. They are therefore continuous in P for any of the valuations
    v(P,ν)."; [Buz07] p. 21: "straight from the definition it follows that if u ∈ A^× then
    Res(Q,P) = Res(u^{−n}Q(uT), P(uT)). This normalisation can be used to renormalise either Q
    or P into A^0⟨T⟩ … Hence if P,Q ∈ A^0⟨T⟩ then Res(Q,P) ∈ A^0"; "Another useful formula is that
    D(uB,P)(T) = D(B,P)(uT) for u ∈ A^×."
  - Lean ↔ source: the crude bound is "if P, Q ∈ A⁰⟨T⟩ then Res ∈ A⁰" with explicit constants;
    the multilinearity estimate is the quantitative form of "polynomials in the a_i, therefore
    continuous"; `dPoly_comp_C_mul_X` is the root-scaling normalisation; `dPoly_C_mul` is
    `D(uB,P)(T) = D(B,P)(uT)`; `norm_coeff_dPoly_le_pow` is Buzzard's renormalisation into the
    unit ball at the rescaled variable `ϖ^m T`.
  - Discharged by: `Matrix.det_apply` (Determinant/Basic:63) + `Polynomial.gaussNorm` at radius
    `Cb⁻¹` with `gaussNorm_mul_le` (ForMathlib Polynomial/GaussNorm.lean:184) and the ultrametric
    `norm_sum_le` on `R[T]` (Gauss norm is nonarchimedean); `Matrix.det_updateRow_add`-type
    multilinearity for the `deg B` rows of `reflect N P`; `resultant_scaleRoots` (:689) with
    `coeff_scaleRoots` (ScaleRoots.lean:33), `resultant_C_mul_right`; `resultant_map_map` along
    `T ↦ λT`; `PseudoUniformizer.isMultiplicative`, `norm_zpow`.
  - Sizing: source 8 lines; expect ~400 LOC (the analytic core of the tranche).
  - Attacks: [1] crude bound with `Cb < 1`? stated with `1 ≤ Cb` (else `(Cb)^j` would not
    dominate the `1` entries) ✓; [2] edges: `deg B = 0` (`B = 0` since `B(0)=0`): `dPoly = 1`,
    bounds `C^0·… ≥ 1` ✓; `j = 0`: `coeff 0 = 1 ≤ C^d` ✓; [3] `norm_coeff_dPoly_le_pow` needs
    `P.coeff 0 = 1` (so that `y_0 = 1` has norm `≤ C`) and `B(0) = 0` (so that `B' = ϖ^{−m}B(ϖ^mX)`
    has coefficients `b_iϖ^{m(i−1)}`, `i ≥ 1`, of norm `≤ Cb`) — both present; [4] drift:
    Buzzard's `Res(Q,P) = Res(u^{−n}Q(uT), P(uT))` is our `dPoly_comp_C_mul_X` after the
    resultant's homogeneity `resultant_C_mul_right` ✓ (re-derived this session:
    `Res(scaleRoots f λ, scaleRoots g' λ) = λ^{Nd}Res(f, g')` with `g' = λ^{−d}(1 − TB(λX))`);
    [5] `resultant_scaleRoots (f g : R[X]) (r : R) : resultant (f.scaleRoots r) (g.scaleRoots r) =
    r ^ (f.natDegree * g.natDegree) * resultant f g` read at :689 ✓ (natDegree-parametrised —
    `natDegree (reflect N P) = N` needs `IsUnit (P.coeff 0)` ✓ present). SURVIVED.
- **L-C4** (leaf, project): `dSeries`, `tendsto_coeff_dPoly_trunc`, `dSeries_coe`,
  `norm_coeff_dSeries_sub_le`, `IsEntire.dSeries`, `dSeries_mul` — Coleman.lean:182–231.
  - Source: [Bel] p. 68: "This allows us, if P = ∑_{i=0}^∞ a_iT^i ∈ R{{T}} is such that P(0) = 1,
    to define D(B,P) = lim_{n→∞} D(B,P_n) with P_n the polynomial ∑_{i=0}^n a_iT^i, and to check
    that the formal series D(B,P) belongs to R{{T}} – see Exercise II.2.2. With this extension of
    the definition, one obtains by passage to the limit in the above lemma: Lemma II.2.14. … (i)
    D(B,PQ) = D(B,P)D(B,Q)."  Exercise II.2.2 (bellaiche.txt 2364–2368): "Let F_n be a sequence
    of power series in R{{T}}. Assume that for every ν ∈ R, F_n is Cauchy for the topology
    defined by v(·,ν). Then show that there exists an F in R{{T}} such that … (F_n) converges to F".
  - Lean ↔ source: `dSeries B F := mk (fun j ↦ limUnder atTop (coeff j ∘ dPoly B (trunc (N+1) F) N))`
    is "`lim D(B,P_n)`"; Cauchy-ness from L-C3's multilinearity estimate with
    `δ = ‖a_{N+1}‖ → 0`; entireness from `norm_coeff_dPoly_le_pow` uniformly in `N`
    (`C_m(trunc) ≤ C_m(F)`); multiplicativity by passage to the limit in `dPoly_mul`.
  - Discharged by: L-C3, `cauchySeq_tendsto_of_complete`, `Filter.Tendsto.limUnder_eq`,
    `PowerSeries.trunc`, `coeff_trunc`, `Polynomial.coe_mul`, coefficient-sup convergence of
    `trunc F · trunc G → FG`.
  - Sizing: source 6 lines + an exercise; expect ~350 LOC.
  - Attacks: [1] `limUnder` needs `Nonempty R` (from `Zero`) — compiled ✓; if the sequence did
    not converge `limUnder` is junk — `tendsto_coeff_dPoly_trunc` supplies convergence under
    `‖a_k‖ → 0` and `‖a_k‖ ≤ C` — both follow from entireness (and `a_0 = 1` gives `C ≥ 1`);
    [2] edges: `F` a polynomial (then the sequence is eventually constant by `dPoly_succ` ⇒
    `dSeries_coe`) ✓; `B = 0` ✓; [3] `dSeries_mul` needs both `F(0) = G(0) = 1` (for the natDegree
    bookkeeping of `dPoly_mul`) ✓ present; [4] drift: [Bel] II.2.14 (i) is stated for `B,P ∈ R[T]`
    polynomial and `Q ∈ R{{T}}` — ours is more general (both entire), obtained by the same limit;
    [5] `tendsto_coeff_dPoly_trunc` as stated needs `hFt : ‖a_k‖ → 0` — for entire `F` from
    `isEntire_iff` at `c = 1` ✓. SURVIVED.
- **L-C5** (leaf, project): `evalT_one_dSeries_bQ_eq_of_eq_mul_add`, `isUnit_evalT_one_dSeries_bQ_iff`,
  `isGoodZero_dSeries_bQ` — Coleman.lean:233–262.
  - Source: [Bel] Lemma II.2.14 (ii): "D(1−P*,Q+CP)(1) = D(1−P*,Q)(1)" for `C,Q ∈ R{{T}}`;
    [Bel] Prop II.2.15 (verbatim): "Let P ∈ R{{T}} with P(0) = 1, and suppose that one can write
    P = QS with Q ∈ R[T] such that Q(0) = 1, and S ∈ R{{T}}. Assume that the ideal generated by Q
    and S is the unit ideal. Let n be the degree of Q. Then D(1−Q*,P)(T) has a good zero of
    order n at 1."  Proof: "D(1−Q*,P)(T) = D(1−Q*,Q)(T)D(1−Q*,S)(T) = (1−T)^nD(1−Q*,S)(T) so it
    suffices to prove that D(1−Q*,S)(1) is a unit."
  - Lean ↔ source: II.2.14 (ii) is used in the form `S = Qq + r ⇒ D(1−Q̃*,S)(1) = D(1−Q̃*,r)(1)`
    (Euclidean division supplies the `C = q`); "`D(1−Q*,S)(1)` is a unit" is *proved* via the
    unit criterion `⟺ (Q,S) = R{{T}}` (L-B3 + L-C2's polynomial criterion) rather than via
    `D(1−Q*, A)` for the Bézout coefficient `A` (whose constant term is not `1`, so Bellaïche's
    `D(·, A)` is undefined in his own convention — a small gap in the source, closed here);
    the good zero then follows from `dSeries_mul`, `dPoly_bQ_self` and `IsGoodZero.mul`-type
    transfer (the `(1−T)^n` factor has a good zero of order `n` at `1`: `Δ^n((1−T)^n)(1) = (−1)^n`).
  - Discharged by: L-B2, L-B3, L-C2, L-C4; dominated convergence
    `tendsto_tsum_of_dominated_convergence` (mathlib) with the uniform bound of L-C3 for the
    evaluations at `1`; Martin's `norm_eq_max_of_eq_mul_add_of_isMulDistinguished`
    (MulWeierstrassDivision.lean:71) for `r_N → r` (remainders of the truncations).
  - Sizing: source ~12 lines; expect ~300 LOC.
  - Attacks: [1] is `evalT 1` of `dSeries` even defined (summable)? yes by `IsEntire.dSeries`
    ✓ (hypothesis `hS : IsEntire S`); [2] edges: `Q = 1` (`n = 0`): `bQ = 0`, `dSeries 0 S = 1`,
    good zero of order `0` at `1` means `IsUnit 1` ✓, and `IsEntireCoprime 1 S` ✓ both sides true;
    `S = 1` ✓; [3] `hS0 : coeff 0 S = 1` needed for `dSeries` conventions; in II.2.15 `S(0) = 1`
    follows from `P(0) = Q(0) = 1` ✓ consistent; [4] drift: Bellaïche's `D(1 − Q*, ·)` uses the
    un-normalised `1 − Q*` whose constant term is `1 − Q*(0) ≠ 0` in general — then `1 − Q*`
    has nonzero constant term and `Q*(φ)/Q*(0)` in the proof of II.2.18 shows the intended
    polynomial is `1 − Q*/Q*(0)` = our `bQ`; recorded as a normalisation slip in the source,
    harmless (both give `(1−T)^n` in (ii) since `Q*(t_i) = 0`); [5] `tendsto_tsum_of_dominated_convergence`
    verified: `Mathlib/Analysis/Normed/Group/Tannery.lean:40`. SURVIVED.
- **L-C6** (leaf, project): `IsCompactoid.aeval`, `charPowerSeries_aeval` — Coleman.lean:267–283.
  - Source: [Bel] Prop II.2.16 (verbatim): "Let M be an R-module satisfying property (Pr) and φ
    be a compact operator of M. Let Q(T) be a polynomial with Q(0) = 0. Then D(Q, det(1−Tφ)) =
    det(1−TQ(φ))."  Proof: "Since Q(0) = 0, Q(φ) is compact and the right hand side of the
    equality makes sense. To prove it, we are reduced as usual to the case where M is
    orthonormalizable, and then to the case where φ is of finite rank."
  - Lean ↔ source: on `c(I,R)` (orthonormalisable) for compactoid `u`; finite rank via row
    truncations `π_S u`, whose `B(π_S u)` is row-supported on `S` with `S × S` block `B(A_S)`;
    L-C2's finite case; limits by `norm_charCoeff_sub_le` on both sides and L-C4's Lipschitz
    estimate on `D`.
  - Discharged by: `IsCompactoid.add/smul/comp_right` (Riesz.lean:618/647, Matrix.lean:550),
    `tendsto_truncation_comp` (Matrix.lean:503), `charCoeff_eq_det_coeff` (Fredholm.lean:491),
    `norm_charCoeff_sub_le` (Fredholm.lean:373), `Matrix.charpolyRev_aeval` (L-C2),
    `norm_coeff_dSeries_sub_le` (L-C4), `charPowerSeries_isEntire` (for the bounded-coefficient
    hypotheses), `Polynomial.aeval` algebra on `c(I,R) →L[R] c(I,R)`.
  - Sizing: source 8 lines; expect ~300 LOC.
  - Attacks: [1] `(π_S u)^k` has `S×S` block `A_S^k`? `(π_S u π_S u)_{S,S} = ∑_{k∈S} A_{sk}A_{kt}` ✓
    since the inner `π_S` restricts the middle index to `S` — checked; rows outside `S` vanish
    ✓ so `charCoeff_eq_det_coeff` applies; [2] edges: `B = 0` (`aeval u 0 = 0`,
    `charPowerSeries 0 = 1 = dSeries 0 _`) ✓; `B = X` (`aeval u X = u`, `dSeries X F = F` by
    `dPoly X P N = Res(reflect P, 1 − TX) = P` — sanity identity, worth a `simp` lemma) ✓;
    [3] `B(0) = 0` necessary: for `B = 1`, `aeval u 1 = 1` is not compactoid and `dPoly 1 P =
    (1−T)^N` depends on the padding — the hypothesis is the source's; [4] drift: none;
    [5] `norm_charCoeff_sub_le (u v) (hu hv) (hn : 1 ≤ n) : ‖c_n u − c_n v‖ ≤ max ‖u‖ ‖v‖^(n−1) * ‖u − v‖`
    read at Fredholm.lean:373 ✓ (coefficient `0` is `1` on both sides). SURVIVED.

## Result T5 — [JN] Theorem 2.2.2 (`PhD/TateFredholm/RieszColeman.lean`)

### Plain-English proof (source structure)
[JN] Thm 2.2.2 (jn.txt 668–681, p. 10): statement + "Apart from the last sentence, this is (a
minor reformulation of) [Buz07, Theorem 3.3]. To see that u is invertible on Ker Q*(u), note
that det(u| Ker Q*(u)) = Q*(0) ∈ R^×. To see that det(1−Tu|N) = S, write S' = det(1−Tu|N) and
note that F = det(1−Tu|Ker Q*(u)) det(1−Tu|N) = QS'. Hence Q(S−S') = 0, and Q is not a zero
divisor since Q(0) = 1, so S = S'."
[Buz07] Thm 3.3 (buzzard.txt 860–885, pp. 24–25): "The operator v = 1 − Q*(φ)/Q*(0) has a
characteristic power series which has a zero at T = 1 of order n. Applying the previous
proposition to v, we see M = N ⊕ F, where N and F are defined as the kernel and the image of a
projector in the closure of A[v] and hence in the closure of A[φ]. Hence both N and F are
φ-stable. Unfortunately … one can only deduce that Q*(φ)^n is zero on N and invertible on F, so
we are not quite home yet. However, by Proposition 3.2, N is projective of rank n. Moreover, the
characteristic power series of φ on F is coprime to Q, by Lemma 3.1. Hence if G(T) is the
characteristic power series of φ on N, we see that Q divides G. But G and Q have degree n and the
same constant term, and furthermore the leading coefficient of Q is a unit. This is enough to
prove that G = Q."
[Bel] Thm II.2.18 (bellaiche.txt 2601–2611, pp. 70–71): "Let φ' = 1 − Q*(φ)/Q*(0). This is a
compact operator whose Fredholm's determinant P_{φ'} satisfies P_{φ'} = D(1−Q*,P_φ) by Prop.
II.2.16. By Prop. II.2.15, P_{φ'} has a good zero of order deg Q at T = 1. The theorem then
follows from Prop. II.2.17 applied to φ' with a = 1."  Prop II.2.17 is Serre's Prop 12 =
`exists_rieszProjection` (with "N is projective of finite type" by Prop II.1.21 and uniqueness
"N'' = p(N + N') … nilpotent … and invertible … Thus N'' = 0").
[Buz07] Prop 3.2 (buzzard.txt 823–858, pp. 23–24) supplies: finiteness ("Because 1 is compact,
we can choose α : N → N of finite rank such that 1 − α is sufficiently small, and hence α is
invertible and so N is finitely-generated. By Lemma 2.11, N is projective."), the polynomial
`P_N`, the rank ("Reducing the situation modulo a maximal ideal of A we see that the reduction
of P_N must be a power of the reduction of (1−a^{−1}T) … the rank of N at any maximal ideal must
equal the degree of P_N modulo this ideal, and hence the rank is h everywhere") and
`P = P_N P_F` ([Buz07] p. 20: "if M and N both have property (Pr) and φ, ψ compact, then
det(1 − X(φ⊕ψ)) = det(1−Xφ) det(1−Xψ)").

### Lemmas
- **L-D1** (leaf, project): `exists_rieszColemanProjection` — RieszColeman.lean:53.
  - Source: [Bel] Thm II.2.18 + proof (above); [Buz07] Thm 3.3 ("Applying the previous
    proposition to v").
  - Lean ↔ source: `p, w` with `p² = p`, `up = pu`, `Q*(u)^{deg Q}(1−p) = 0`, `Q*(u)w = p` are
    Serre's projector for `φ' = aeval u (bQ Q v)` at `a = 1`, order `deg Q`, unwound:
    `1 − φ' = v⁻¹Q*(u)`, so `(1 − φ')^n(1−p) = 0 ⇔ Q*(u)^n(1−p) = 0` and `(1−φ')w' = p ⇔
    Q*(u)(v⁻¹w') = p`.
  - Discharged by: `exists_rieszProjection` (Riesz.lean:1922; hypotheses: `IsCompactoid u`,
    `1 ≤ h`, `h0`, `hunit` — exactly `IsGoodZero (charPowerSeries φ') 1 n` unfolded), L-C6
    (`charPowerSeries φ' = dSeries (bQ Q v) (charPowerSeries u)`), L-C5 (`isGoodZero_dSeries_bQ`
    after rewriting `charPowerSeries u = Q·S`), L-C6 `IsCompactoid.aeval` (`bQ_coeff_zero`),
    `Polynomial.aeval` algebra: `aeval u (bQ Q v) = 1 − v⁻¹ • aeval u Q.reverse`.
  - Sizing: source 4 lines; expect ~120 LOC.
  - Attacks: [1] `deg Q = 0` (`Q = 1`): `exists_rieszProjection` needs `1 ≤ h` — then take
    `p = 1, w = 1` directly (`Q* = 1`) — the ticket sketch case-splits ✓; [2] edge: `S = 1`
    (`u` finite-rank with `det = Q`): fine; [3] no `IsNoetherianRing` — `exists_rieszProjection`
    has none ✓; the hypothesis `coeff 0 S = 1` follows from `hF` and `hQ0` but is kept explicit
    (cheap, avoids a derivation in every consumer); [4] drift: [JN]/[Bel] work on (Pr)/ON-able
    `M`; ours is `c(I,R)` — the model space, transported later if needed (`charPowerSeries_conj`);
    [5] `exists_rieszProjection` signature read at Riesz.lean:1922–1927 ✓ shape matches.
    SURVIVED.
- **L-D2** (leaf, project): `exists_rieszProjection_isOpLimit`, `commute_of_isOpLimit_aeval`
  — RieszColeman.lean:67–89.
  - Source: [JN] Thm 2.2.2: "The idempotent projectors M → Ker Q*(u) and M → N lie in the closure
    of R[u] ⊆ End_{R,cts}(M)."  [Bel] II.2.17: "Let R' be the closure of the subring of End_R(M)
    generated by φ … It follows that p and q are orthogonal projectors in R'." and "Moreover, N and
    F are stable by every operator u ∈ End_R(M) that commutes with φ. … The last sentence is
    clear since we defined [N] and F [as] image of projectors that are power series in φ."
  - Lean ↔ source: `∃ pol : ℕ → R[X], IsOpLimit (fun k ↦ aeval u (pol k)) p` is "p ∈ closure of
    R[u]" for the operator norm; the commutation lemma is the "last sentence".
  - Discharged by: the construction inside `exists_rieszProjection` (Riesz.lean:1922–1970: `N_s`
    are `IsOpLimit` of `resolventPartialSum` = polynomials in `u`; `e, f, p = e^h` are ring
    expressions in them), `IsOpLimit.add/comp_left/comp_right/const/unique` (Riesz.lean:519–560),
    `IsOpLimit` closure under products (from `comp_left/right`); commutation: `IsOpLimit.unique`
    applied to `p * w` and `w * p` (both limits of `aeval u (pol k) * w = w * aeval u (pol k)`).
  - Sizing: source 2 lines; expect ~150 LOC (re-run of the construction with the extra
    invariant, or a refactor of `exists_rieszProjection` exposing it — worker's choice, recorded).
  - Attacks: [1] is `p` really a limit of polynomials, not just in the *closed subalgebra*? yes:
    products of `IsOpLimit`s of polynomials are `IsOpLimit`s of polynomial products
    (operator-norm submultiplicativity, `opNorm_mul_le`) ✓; [2] edge `h = 1`; `a = 0` (then
    `p = 1`?) fine; [3] no extra hypothesis; [4] drift: none; [5] `IsOpLimit.comp_left/right`
    read at Riesz.lean:547/557 ✓ (they compose with a fixed operator on one side — for the
    product of two limits use `add`/`comp` + `unique` with a telescoping bound; sketched in
    the ticket). SURVIVED.
- **L-D3** (leaf, project): `restrictRange`, `IsCompletelyContinuous.restrictRange`,
  `finite_range_of_one_sub_nilpotent`, `projective_range_of_finite` — RieszColeman.lean:91–130.
  - Source: [Bel] Prop II.1.21 (verbatim, bellaiche.txt 2243–2254): "Let P be an R-module with
    property (Pr) and φ a compact operator on P such that 1−φ is nilpotent. Then P is finite and
    projective. Proof — If (1−φ)^n = 0 on P, then by expanding we see that the identity is
    compact on P. … there exists a projector q in End_R(M) whose image is finite free and such
    that |u−qu| < 1/|p| … which shows that the morphism pqu|_P = pq : P → P is invertible. Hence
    the image pq(P) of that morphism is P. Therefore P is a submodule of p(q(M)) which is finite
    since q(M) is, and P itself is finite. By Prop. II.1.20, it is also projective."  [Bel] Prop
    II.1.20: "If a finite R-module has property (Pr), then it is projective. Proof — … choose a
    surjective continuous map f : A^r → P and apply Exercise II.1.19 to α = Id_P."
  - Lean ↔ source: `P = range p` for a continuous idempotent `p` of `c(I,R)` (a direct summand
    of a potentially ON-able module = property (Pr) in [Bel]'s sense) — stated on the idempotent
    because `Pr.lean`'s `HasPr` indexes its model space by a `Set` of the module itself (the
    obstruction recorded at Riesz.lean:2305–2310: "its model-space index must be a subset of the
    module, which small N inside a large c(I, K) need not admit").
  - Discharged by: the proof of `finite_projective_of_one_sub_compact_nilpotent` (Pr.lean:141–187,
    read: Neumann series `exists_inverse_of_norm_id_sub_lt_one`, geometric factorisation
    `mul_geom_sum`, `IsCompletelyContinuous` on `↥p.range` with `CompleteSpace` from
    `isClosed_range`-of-idempotent, `IsBoundedSMul.of_norm_smul_le`), `HasPr.projective`'s
    proof (Pr.lean:132–139) with `exists_lift_cSpace` (Pr.lean:24, private — to expose) applied
    to `f : (Fin n → R) →L c(I,R)`… lifted through `p`, `Module.Projective.of_split`.
  - Sizing: source 12 + 4 lines; expect ~250 LOC (+ the `Pr.lean` refactor).
  - Attacks: [1] `restrictRange` well-defined? membership proof compiled ✓; [2] edges: `p = 0`
    (`range = ⊥`, finite/projective trivially; `1 − φ` nilpotent on `0` vacuous) ✓; `p = 1`
    (then `c(I,R)` finite ⇒ `I` finite — consistent: `1 − φ` nilpotent on `c(I,R)` forces the
    identity compact) ✓; [3] `finite_range_of_one_sub_nilpotent` needs only `IsCompletelyContinuous
    φ` (not `IsCompactoid`) — matches `finite_projective_of_one_sub_compact_nilpotent`; the
    unused `[IsNoetherianRing R]` there is dropped here ✓ (its own proof comment confirms);
    [4] drift: none; [5] `exists_lift_cSpace` is `private` — ticket D2 exposes it (rename recorded).
    SURVIVED.
- **L-D4** (leaf, project): `charPowerSeries_add_of_mul_eq_zero`,
  `exists_polynomial_charPowerSeries_of_range_le` — RieszColeman.lean:138–160.
  - Source: [Buz07] p. 20 (verbatim): "if M and N both have property (Pr) and φ : M → M and
    ψ : N → N are compact, then det(1 − X(φ⊕ψ)) = det(1 − Xφ) det(1 − Xψ)" (stated without proof:
    "we leave it as an exercise for the reader"); [Buz07] Prop 3.2 proof: "Moreover, P_N is a
    polynomial because N is finitely-generated".
  - Lean ↔ source: `v = u(1−p)`, `w = up` are `φ ⊕ 0` and `0 ⊕ ψ`; `vw = wv = 0`; the polynomial
    claim is stated for range in a span of `s.card` vectors.
  - Discharged by: `fredholmDet_mul` (Riesz.lean:1768: `fredholmDet (u + v − uv) = fredholmDet u *
    fredholmDet v`) at `a•v, a•w` (`a•v * a•w = 0`), `fredholmDet_smul`/`charCoeff_smul`
    (Riesz.lean:1386/1396), `IsEntire.evalT_mul`, `charPowerSeries_isEntire`, and L-B4's
    identity theorem at `a = ϖ^k`; polynomiality: `minor u S = det` of `S×S` coordinates of
    vectors in `span s` — factor the `S×S` matrix as `(|S| × card s)·(card s × |S|)`, extend by
    zero rows/columns to square factors, `Matrix.det_mul` with a zero row ⇒ `0` for `|S| > card s`
    ⇒ `charCoeff u m = 0` for `m > card s`.
  - Sizing: source 1 line (exercise); expect ~250 LOC.
  - Attacks: [1] is `fredholmDet_mul`'s expression right? `1 − (a v + a w − a v · a w) =
    (1 − a v)(1 − a w)` and `a v · a w = a²vw = 0` ✓; [2] edge `v = 0`: `charPowerSeries 0 = 1` ✓;
    `s = ∅`: `u = 0` ✓; [3] both `vw = 0` and `wv = 0` assumed (only `vw = 0` used in the
    factorisation `(1 − Tv)(1 − Tw) = 1 − T(v+w) + T²vw`; `wv = 0` kept for symmetry — flagged as
    possibly droppable; harmless); [4] drift: none; [5] `fredholmDet_mul {u v} (hu) (hv) :
    fredholmDet (u + v − u * v) = fredholmDet u * fredholmDet v` read at Riesz.lean:1768 ✓.
    SURVIVED.
- **L-D5** (leaf, project): `isEntireCoprime_iff_isUnit_aeval_reverse` — RieszColeman.lean:165.
  - Source: [Buz07] Lemma 3.1 (verbatim): "With A, M, φ and P as above, if Q(X) ∈ A[X] is monic
    then Q and P generate the unit ideal in A{{X}} if and only if Q*(φ) is an invertible operator
    on M."  Preceded by "Lemma A4.1 of [10] goes through unchanged, and we recall it here".
    **Source gap**: Coleman's proof (A4.1) is not to hand.  Fallback chain: cross-reference —
    [Bel] has no such lemma but supplies all ingredients (II.2.14–II.2.16, Serre 11); wider search
    — no open copy of [Col97] found (Springer paywall).  The proof below is the planner's
    reconstruction from [Bel]'s identities, flagged for the user; no `/expert-review` needed
    since every step is a proved leaf of this tree.
  - Lean ↔ source: Buzzard's `Q` monic with `P = det(1−Tφ)`; ours `Q(0) = 1` with unit leading
    coefficient `v` (Buzzard's normalisation differs by the unit `v`; `Q*(φ)` invertible is
    invariant).
  - Reconstructed proof: `Q*(u)` invertible ⟺ `1 − φ'` invertible (`1 − φ' = v⁻¹Q*(u)`) ⟺
    `P_{φ'}(1)` unit (Serre Prop 11, `isUnit_one_sub_smul_iff_isUnit_evalT` at `a = 1`) ⟺
    `D(1−Q̃*, P_u)(1)` unit (L-C6) ⟺ `(Q, P_u) = R{{T}}` (L-C5 unit criterion).
  - Discharged by: `isUnit_one_sub_smul_iff_isUnit_evalT` (Riesz.lean:1821), L-C6, L-C5, L-C6
    `IsCompactoid.aeval`.
  - Sizing: source 0 lines (cited); reconstruction ~80 LOC.
  - Attacks: [1] direction (⇒) sanity: `Q = 1 − aT` (`v = −a`… with `Q(0)=1`), `Q* = X − a`,
    `Q*(u) = u − a` invertible ⟺ `(1 − aT, P_u) = 1` ⟺ `P_u(a⁻¹)` unit (for `a` a unit) ⟺
    `1 − a⁻¹u` invertible (Serre 11) ✓ consistent; [2] edge `Q = 1`: both sides true ✓; [3] no
    hidden hypothesis beyond `Q(0) = 1`, unit leading coefficient — Buzzard has "monic";
    [4] drift: statement matches Buzzard up to the unit normalisation; [5] all four `⟺` steps
    are leaves of this tree ✓. SURVIVED (flagged: reconstructed proof).
- **L-D6** (internal, then leaves): the refinements `IsRieszColemanProjection.finite/projective/
  exists_polynomial/charPowerSeries_eq_mul/isEntireCoprime_range/rankAtStalk/
  charPowerSeries_mul_one_sub/charPowerSeries_mul/aeval_reverse_mul_one_sub/ker_aeval_reverse/
  isUnit_mul_one_sub_add/eq_range_of_isTopCompl/isUnit_aeval_reverse_of_isEntireCoprime`
  — RieszColeman.lean:179–290.
  - Source: [Buz07] Prop 3.2 / Thm 3.3 and [JN] 2.2.2's last sentence, quoted above; [Bel]
    II.2.17 uniqueness; [JN] Thm 2.2.13 (⇐) (jn.txt 822–829): "It remains to show that for every
    multiplicative polynomial P of slope ≤ h, P*(u) is invertible on N. By Lemma 2.2.7 P and S
    are relatively prime. Since S = det(1−Tu|N) (by Theorem 2.2.2), it follows from [Buz07,
    Lemma 3.1] that P* is invertible on N, as desired."
  - Sub-decomposition (mirrors Buzzard's proof order):
    - `.finite`, `.projective` ← L-D3 with `φ = aeval u (bQ Q v)` (`(1 − φ)^n(1−p) = 0` is `nil`).
    - `.exists_polynomial` ← L-D4 (range of `u(1−p)` ⊆ `(1−p).range`, finitely generated by
      `.finite`).
    - `.charPowerSeries_eq_mul` ← L-D4 (`(u(1−p))(up) = 0 = (up)(u(1−p))`).
    - `.isEntireCoprime_range` ← L-D5 applied to `ψ = up` (`aeval (up) Q* = v(1−p) + Q*(u)p`,
      invertible with inverse `v⁻¹(1−p) + w`-type from `inv`).
    - `.rankAtStalk` ← [Buz07] Prop 3.2's mod-`𝔪` argument: for a maximal `𝔪`, `N ⊗ k(𝔪)` is a
      `k(𝔪)`-space of dimension `rankAtStalk N 𝔪` (`rankAtStalk_eq_finrank_tensorProduct`);
      `φ'` is unipotent there ⇒ `det(1 − Tφ' | N⊗k) = (1 − T)^{rank}`
      (`isNilpotent_charpoly_sub_pow_of_isNilpotent` over the reduced `k(𝔪)`); meanwhile
      `det(1 − Tφ' | N) = D(1−Q̃*, G) = (1−T)^n·H'` with `H'(1)` a unit (L-C5 + L-D4 + L-B4
      `IsGoodZero.of_mul`); reducing the polynomial identity mod `𝔪` and comparing orders of
      vanishing at `1` in `k(𝔪)[T]` gives `rank = n`.  The comparison `det(1−Tφ'|N)` ↔ the
      algebraic determinant on `N ⊗ k(𝔪)` goes through the trace trick: `u(1−p) = a ∘ b` with
      `a : c(Fin r, R) → c(I,R)`, `b : c(I,R) → c(Fin r,R)` for a surjection `R^r → N`, so
      `charPowerSeries (u(1−p)) = charPowerSeries (b ∘ a) = charpolyRev (b∘a)` (`charPowerSeries_comm`,
      `charCoeff_eq_det_coeff`) and `b ∘ a` is an `r × r` matrix whose reduction mod `𝔪` is the
      algebraic picture.
    - `.charPowerSeries_mul_one_sub` ← `Q ∣ G` in `R{{T}}` (`P_u = G·H = Q·S`, `(Q,H) = 1`:
      `G = (aQ)G + b GH = Q(aG + bS)`), `G = Q·K` with `K` a polynomial (uniqueness of Euclidean
      division, L-B2), `deg G ≤ n` from `.rankAtStalk` (localisation: `N_𝔪` free of rank `n`
      ⇒ `det(1 − T u|N_𝔪)` has degree `≤ n`, coefficients above `n` vanish in every `R_𝔪`
      ⇒ vanish, `Module.eq_zero_of_localization_maximal`), then `K` constant `= 1` (`Q(0) = 1 =
      G(0)`, unit leading coefficient).
    - `.charPowerSeries_mul` ← `Q·S = Q·H` and `Q` is a unit of `R⟦T⟧` (`PowerSeries.isUnit_iff_constantCoeff`).
    - `.aeval_reverse_mul_one_sub` ← Cayley–Hamilton for `b ∘ a` (`Matrix.aeval_self_charpoly`)
      transported to `N` (`reflect_r G = X^{r−n}·Q*` and `u` invertible on `N`).
    - `.ker_aeval_reverse` ← `Q*(u)(1−p) = 0` and `Q*(u)w = p` (`x ∈ ker ⇒ px = Q*(u)wx = wQ*(u)x = 0`).
    - `.isUnit_mul_one_sub_add` ← `Q*(u) = 0` on `N` and `Q*(0) = v`: `u·(−v⁻¹(Q*(u) − v)/u…)`:
      `v·1 = Q*(u) − u·(∑_{i≥1} q_{n−i}… )` on `N`, explicit inverse.
    - `.eq_range_of_isTopCompl` ← [Bel] II.2.17's argument on `N'' = p(F' ∩ …)`.
    - `.isUnit_aeval_reverse_of_isEntireCoprime` ← L-D5 for `ψ = up` with `charPowerSeries ψ = S`
      (`.charPowerSeries_mul`).
  - Sizing: source ~30 lines across Buzzard 3.2/3.3 and JN; expect ~900 LOC (D5–D8 tickets).
  - Attacks (composition): [1] could the children hold and `G = Q` fail? The step `deg G ≤ n`
    needs rank `= n` at *every* maximal ideal — `.rankAtStalk` is stated at every prime ✓; the
    localisation step needs `N` finitely presented (f.g. projective ⇒ finitely presented ✓ mathlib
    `Module.finitePresentation_of_projective`) for `N_𝔪` free of rank `n` (`free_of_flat_of_isLocalRing`)
    ✓; [2] edge `n = 0` (`Q = 1`): `N = 0`, `G = 1`, all statements degenerate correctly (`rank 0`);
    [3] over a ring with idempotents (`R = K × K`) the rank is constant `n` — consistent with
    Buzzard's "rank h everywhere"; the naive shortcut "P_q = (1−T)^n" was checked and rejected at
    planning (idempotents of non-constant rank), hence the localisation route; [4] source drift:
    [Buz07] proves rank via `P_N = (1−a^{−1}T)^h` for a *linear* factor; here the same argument is
    run for `φ'` at the linear factor `(1 − T)` and then transferred to `Q` via `G = QK` and `D`
    — a genuine reorganisation, but every step is quoted/derived; [5] `isNilpotent_charpoly_sub_pow_of_isNilpotent`
    (Charpoly/Coeff:361) read ✓; `rankAtStalk_eq_finrank_tensorProduct` (FreeLocus:278) ✓;
    `Matrix.aeval_self_charpoly` (Charpoly/Basic:211) ✓. SURVIVED (largest risk of the board;
    D6 ticket carries a detailed sketch).

## Result T6 — the vertex factorisation, norm level (`PhD/TateFredholm/SlopeFactor.lean`)

### Plain-English proof (source structure)
[Bel] Def II.2.3–II.2.4, Lemma II.2.5 (bellaiche.txt 2369–2388, pp. 64–65); Thm II.3.6
(bellaiche.txt 2985–3070, pp. 72–74, ~85 lines): construct `P_n` inductively with
`P_1 = ∑_{i≤N} a_iT^i`, `P_{n+1} = P_n + S_n` where `F = P_nG_n + S_n` is the Euclidean division;
the estimates (II.3.5)–(II.3.6) make `(P_n)`, `(G_n)` Cauchy; the limit satisfies `F = P_∞G_∞`
with `P_∞` `ν`-dominant of degree `N` and `N(G_x,ν) = 0`.  [Ke09] Prop 3.2.2 (arXiv
math/0609645 §3.2, fetched): "Fix r<r₀ and m∈ℤ≥0. Let R∈F{T} be a twisted polynomial such
that v_r(R−T^m)>v_r(T^m). Then R can be factored uniquely as PQ, where P∈F{T} has degree
deg(R)−m and all slopes less than r, Q∈F{T} is monic of degree m and has all slopes greater
than r, v_r(P−1)>0, and v_r(Q−T^m)>v_r(T^m)." with proof "Define P₀=1 and Q₀=T^m. Given P_l and
Q_l, write R−P_lQ_l=∑ᵢa_iT^i, then put X_l=∑_{i≥m}a_iT^{i−m}, Y_l=∑_{i<m}a_iT^i and set
P_{l+1}=P_l+X_l, Q_{l+1}=Q_l+Y_l." — the same iteration.  [JN] Def 2.2.5 and Lemma 2.2.7 give
the slope-factorisation vocabulary; [JN] Lemma 2.2.9's proof reduces to "if Q_1 and Q_2 are two
multiplicative polynomials of slope ≤ h, then so is Q_1Q_2".

### Lemmas
- **L-E1** (leaf, project): `IsDominantIndex`, `IsDominantPoly`,
  `exists_isDominantPoly_of_isUnit_leadingCoeff`, `IsDominantPoly.mul`,
  `norm_coeff_r_mul_pow_le_of_eq_mul_add` — SlopeFactor.lean:39–86.
  - Source: [Bel] Def II.2.3: "We write N(F,ν) for the largest integer N such that
    v_p(a_N) − Nν = inf_{n∈N}(v_p(a_n) − nν)"; Def II.2.4: "A polynomial Q(T) ∈ R[T] is called
    ν-dominant if (i) Q has degree N(Q,ν) (ii) The dominant term of Q is invertible."; Lemma
    II.2.5: "If Q(T) ∈ R[T] is a polynomial whose dominant term is invertible, there exists
    ν_0 ∈ R such that for all ν ≥ ν_0, Q is ν-dominant."; [JN] Lemma 2.2.9 proof (above); [Bel]
    Prop II.2.8: "v(S,ν) ≥ v(F,ν)".
  - Lean ↔ source: `ρ = p^{ν}`-multiplicative form: `‖a_k‖ρ^k ≤ ‖a_N‖ρ^N`, strict for `k > N`;
    `IsDominantPoly.mul` is the polynomial fact behind [JN] 2.2.9; the remainder estimate is
    (II.2.1)/(II.2.8) at radius `ρ`.
  - Discharged by: `Polynomial.norm_mul_of_isMulDistinguished` (MulDistinguished.lean:221,
    Martin Lemma 1.26: the product's norm is attained at the sum of the distinguished degrees)
    with `isMulDistinguished_toRestricted_of_monic`-type conversion (dominant + multiplicative
    unit leading coefficient ⇒ Martin-distinguished at radius `ρ` after unit rescaling),
    `norm_eq_max_of_eq_mul_add_of_isMulDistinguished` (MulWeierstrassDivision.lean:71).
  - Sizing: source ~12 lines; expect ~200 LOC.
  - Attacks: [1] `IsDominantPoly.mul` needs the leading coefficients *multiplicative* for
    Martin's lemma, whereas the definition only asks invertible — [Bel] Ex II.3.4/II.3.5 flag
    exactly this ("a polynomial … can be ν-dominant without satisfying v_p(a_N) + v_p(a_N^{−1}) = 0");
    over `A` the leading coefficients in play are `T^λ·(norm-1 unit)`, multiplicative — the
    ticket adds the `IsMultiplicative` hypothesis to `.mul` if the proof needs it (B2 candidate
    otherwise; statement to be tightened at execution, recorded); [2] edges: `P` constant unit
    (`natDegree 0`, dominant index `0`) ✓; `ρ → ∞` recovers "leading coefficient dominates" ✓;
    [3] `0 < ρ` needed for strictness arithmetic ✓ present; [4] drift: none; [5] Martin's lemma
    names read this session ✓. SURVIVED (with the recorded tightening).
- **L-E2** (leaf, project): `exists_isDominantFactorization` — SlopeFactor.lean:89.
  - Source: [Bel] Thm II.3.6 (ii) and its existence proof, verbatim key steps: "We start the
    construction by induction by setting P_1 = ∑_{i=0}^N a_iT^i. … we set P_{n+1} = P_n + S_n
    … v(F−P_{n+1},ν) ≥ v(F−P_1,ν) > v(F,ν), (II.3.9) … v(G_{n+1}−1,ν) ≥ v(F−P_1,ν) − v(F,ν),
    (II.3.11) … the sequence (P_n) is Cauchy for v(·,ν) … hence converges … to a limit
    P_∞ ∈ R[T]. Similarly condition (II.3.6) shows that G_n also converges to a limit G_∞ … Going
    to the limit in (II.3.2), we obtain F = P_∞G_∞. … G_∞ is in R{{T}}. By going to the limit in
    (II.3.10), v(P_∞,ν) = v(F,ν) and since N(F,ν) = N, and the coefficient of T^N in P_∞ is 1,
    P_∞ is strongly ν-dominant … Since F(0) = P_∞(0)G_∞(0), P_∞(0) is invertible in R, and we
    can set P = P_∞(0)^{−1}P_∞, G = P_∞(0)G_∞. Then F = PG with P(0) = 1."
  - Lean ↔ source: the norm-level existence statement (the pointwise "strongly" and "for all x"
    conditions replaced by the radius-`ρ` dominant index of `P` and `‖g_k‖ρ^k < 1` for `k ≥ 1`
    — [Bel]'s (II.3.11) at the limit); `hmul` (dominant coefficient multiplicative) is what makes
    (II.2.8)'s quotient estimate available ("if the dominant term of B is multiplicative").
  - Discharged by: L-B2 (division at each step), L-E1 estimates, `Metric.complete_of_cauchySeq_tendsto`-style
    coefficientwise completeness of `Restricted R ρ` (`PowerSeries.Restricted` `CompleteSpace`
    via `Complete.lean`), `PowerSeries.Restricted.norm_le_iff` (GaussNorm.lean:178); cross-radius
    entireness of the limit `G` as in L-B2 (uniqueness of division at larger radii).
  - Sizing: source ~60 lines; expect ~450 LOC (largest single leaf of tranche E).
  - Attacks: [1] convergence requires the strict gap `v(F − P_1, ν) > v(F, ν)` — this is exactly
    "strict for `k > N`" in `IsDominantIndex` ✓; without strictness the iteration stalls
    (counter-scenario: `F = 1 + T + T²…` at the radius where two terms tie) — hypothesis
    necessary; [2] edges: `N = 0` (`P = 1`, `G = F`, need `‖a_k‖ρ^k < 1` for `k ≥ 1` — given) ✓;
    `F` a polynomial (then the iteration terminates) ✓; [3] `hunit` + `hmul` both used (unit for
    normalising `P(0) = 1`, multiplicative for the quotient estimate); [4] drift: the norm-level
    reformulation is deliberate (plan §Generality); the field case reproduces [Bel]'s pointwise
    statement; [5] Martin's division produces `q` restricted at radius `ρ`, matching (II.3.7)
    `v(G_{n+1} − 1, ν) ≥ …` ✓. SURVIVED.
- **L-E3** (leaf, project): `IsDominantFactorization.isEntireCoprime` — SlopeFactor.lean:100.
  - Source: [JN] Lemma 2.2.7 (verbatim): "Let R be a Banach–Tate ring with a fixed
    multiplicative pseudo-uniformizer ϖ and let h ∈ Q≥0. Let S be a Fredholm series of slope > h
    and Q a multiplicative polynomial of slope ≤ h. Then Q and S are relatively prime."  Its
    proof is via Coleman's resultant and the Gelfand spectrum ("Pick x ∈ M(R) and specialize to
    K_x … By [Ber90, Corollary 1.2.4] …"), out of reach; the norm-level statement is proved
    instead by Weierstrass division ([Bel] Cor II.2.9's mechanism at radius `ρ`).
  - Lean ↔ source: "`S` of slope `> h`" ↦ "`‖g_k‖ρ^k < 1` for `k ≥ 1`" (`G` is a unit of
    `R⟨ρ⁻¹T⟩`, Neumann series); "`Q` of slope `≤ h`" ↦ `ρ`-dominant.
  - Reconstructed proof: `G·G⁻¹ = 1` in `Restricted R ρ`; divide `G⁻¹ = Pq' + r'` (Martin at
    radius `ρ`, `P` distinguished) and `G = Pq + r` (L-B2); then `r r' ≡ 1 mod P` in `R[T]`, so
    `1 = r'G + P(c − q r')` with entire coefficients.
  - Discharged by: `PowerSeries.Restricted` units (`Units` file / `IsNormMulUnit`, Neumann series
    in the complete normed ring `Restricted R ρ`), Martin's division (`weierstrassDivision_exists_of_isMulDistinguished`),
    L-B2, L-B3 (`isCoprime_of_mul_add_eq_one`).
  - Sizing: source 0 lines at the norm level (planner reconstruction, flagged); expect ~150 LOC.
  - Attacks: [1] is `G` really a unit of `Restricted R ρ`? `‖G − 1‖_ρ = sup_{k≥1}‖g_k‖ρ^k`
    — the *sup* must be `< 1`, not just each term: since `G` is entire, `‖g_k‖ρ^k → 0`, so the
    sup of finitely many `< 1` terms and a tail `< 1` is `< 1` ✓ (this is why `lt_one` per `k`
    suffices; noted for the ticket); [2] edges: `P = 1` trivial; [3] `0 < ρ` needed ✓;
    [4] drift: deliberate reformulation, plan §Generality; [5] the `Restricted R ρ` unit criterion
    verified: `PowerSeries.Restricted.isUnit_of_norm_lt_norm_constantCoeff` and `isUnit_iff`
    (`ForMathlib/…/Restricted/Units.lean:76, :101`). SURVIVED (flagged: reconstructed).

## Result T7 — the application over `A` (`PhD/LWX/TateRiesz.lean`)

### Plain-English proof (source structure)
[LWX] proof of Thm 3.16 (lwx.txt 1641–1663): "To compute Char(P), we work with a bigger
coefficient ring Λ^{>1/p}. … We now conjugate the matrix P by the infinite diagonal matrix
whose diagonal entries are 1,…,1 (t), T,…,T (t), T²,…,T² (t),…; let P' = (P'_{m,n}) denote the
matrix we get this way. Then we have P'_{m,n} ∈ m^{max{⌊m/t⌋−⌊n/pt⌋,0}}_Λ · T^{⌊n/t⌋−⌊m/t⌋}Λ^{>1/p}
⊆ T^{max{⌊n/t⌋−⌊n/pt⌋, ⌊n/t⌋−⌊m/t⌋}}Λ^{>1/p}. In particular, the entries of P' in the n-th column
all lie in T^{⌊n/t⌋−⌊n/pt⌋}Λ^{>1/p}. So Char(P) = Char(P') has the property given in (3.16.1)."
[LWX] Rmk 3.25 (lwx.txt 2112–2118): "We note that the existence of n^±_k in the proof of
Theorem 1.3 in fact implies that, for n = n^±_k, c_n(T) is equal to T^{λ_n} times a unit in
Λ^{>1/p}. Then, a standard factorization argument shows (see e.g. [Ke09, Proposition 3.2.2] for
the argument) that we can factor Char(P) into the following product P_0(X)·P_{(0,1)}(X)·P_1(X)·
P_{(1,2)}(X)··· such that each P_I(X) ∈ Λ^{>1/p}JXK is the characteristic polynomial
corresponding to the component X_I."  [LWX] Step II (lwx.txt 1880–1883): "⌊n_k/t⌋ − ⌊n_k/pt⌋ =
kq − kq/(p−1)… = kφ(q). So if i ∈ Z and n_{k+1} − i ≥ 0, then λ(n_{k+1} − i) ≥ λ(n_{k+1}) −
(k+1)φ(q)i with equality if and only if i ∈ [−t, t]" — the convexity of `λ` at the vertices.

### Lemmas
- **L-F1** (leaf, project): `tateOp`, `matrixCoeff_tateOp`, `norm_matrixCoeff_tateOp_le`,
  `isCompactoid_tateOp` — TateRiesz.lean:48–73.
  - Source: [LWX] Thm 3.16 proof (conjugation display, above); [JN] Def 2.1.5 (jn.txt 517–521):
    "φ is compact if and only if lim_{j→∞} sup_{i∈I} |a_{ij}| = 0".
  - Lean ↔ source: entry at row `(j,n)`, column `(i,m)` is `T^{n−m}M_{(i,m),(j,n)}` = `(D⁻¹PD)ᵀ`
    at `t = 1` blockwise (the `T^{⌊n/t⌋}` of [LWX] is `T^n` here because the halo board's
    weight is `m − ⌊n/p⌋` per block coordinate, `UpDatum.norm_matrix_le`); the row bound is
    [LWX]'s "entries of P' in the n-th column all lie in `T^{⌊n/t⌋−⌊n/pt⌋}`", transposed;
    `IsCompactoid` is [JN]'s compactness criterion.
  - Discharged by: `UpDatum.norm_matrix_le` (UpMatrix.lean:552: `‖M a b‖ ≤ p^{−(a.2 − b.2/p)}`),
    `HaloTate.norm_T_mul` + `norm_ofInt`, `exists_coeffEquiv` (Matrix.lean:134) or the
    `cSpace.ofTendsto`/`mkContinuous` pattern of `UpDatum.op` (UpMatrix.lean:689), row-decay ⇒
    `Tendsto (rowNorm) cofinite (𝓝 0)` via `Set.Finite.subset` as in `Halo.lean`'s `hw_upOp`.
  - Sizing: `UpDatum.op`'s construction was ~60 lines (UpMatrix.lean:640–712); expect ~250 LOC.
  - Attacks: [1] the bound recomputed by hand this session (both cases of `max(m − ⌊n/p⌋, 0)`)
    ✓; [2] edges: `p = 2` excluded by `hp2` (as in the halo board: the entry bound needs it);
    `n = 0` row: bound `p^0 = 1` ✓; `ι` a singleton ✓; [3] `IsCompactoid` needs *cofinite* decay
    on `ι × ℕ`: `p^{−(n−⌊n/p⌋)} → 0` as `n → ∞` and `ι` finite ✓ (`hw_upOp`'s finiteness argument);
    [4] drift: transposition is the plan's deliberate seam (recorded; the prior-B2 log forbids
    the untransposed rescaled `c₀` model); [5] `UpDatum.norm_matrix_le` signature read ✓.
    SURVIVED.
- **L-F2** (leaf, project): `minor_tateOp`, `charPowerSeries_tateOp` — TateRiesz.lean:75–89.
  - Source: [LWX]: "So Char(P) = Char(P')"; [LWX] Thm 3.16: "The characteristic power series
    Char(P) := lim_{n→∞} det(1 − X(P_{i,j})_{i,j=0,…,n−1}) = ∑_{n≥0} c_nX^n ∈ ΛJXK is well defined".
  - Lean ↔ source: `minor (tateOp) S = ofInt (minor (op) S)` (transpose + diagonal conjugation
    over the finite set `S`), hence `charCoeff (tateOp) n = ofInt (charCoeff (op) n)` by
    continuity of the isometry `ofInt` and the halo board's summability `summable_minor_upOp`.
  - Discharged by: `Matrix.det_transpose`, `Matrix.det_units_conj` (Determinant/Basic:192: `det (M N M⁻¹) = det N`), `UpDatum.matrixCoeff_op` (UpMatrix.lean:705),
    `summable_minor_upOp` (Halo.lean:113), `Summable.map`/`tsum` along the continuous ring hom
    `ofIntRingHom` (`norm_ofInt` ⇒ Lipschitz), `PowerSeries.map`, `charPowerSeries_coeff`.
  - Sizing: source 1 line; expect ~150 LOC.
  - Attacks: [1] transposition of `minor`: `minor u S = det (of fun j i : S ↦ matrixCoeff u j i)`
    (Fredholm.lean:33) and the transposed operator's minor is the determinant of the transposed
    block ✓ `det_transpose`; the diagonal factors `T^{n_a}`/`T^{−m_b}` — for a principal minor
    `a, b ∈ S` the products `∏_{a∈S}T^{n_a}·∏_{b∈S}T^{−n_b} = 1` ✓ (same index set); [2] edge
    `S = ∅`: `1 = ofInt 1` ✓; [3] summability over `A` of the minors of `tateOp` is `IsCompactoid`
    + `summable_minor` (needs `IsTate A` ✓ L-A3) — or transported from `summable_minor_upOp`;
    [4] drift: none; [5] `summable_minor_upOp (hp2) (D) (ω) (n)` read at Halo.lean:113 ✓.
    SURVIVED.
- **L-F3** (leaf, project): `IsHaloVertex`, `isDominantIndex_charPowerSeries_tateOp`,
  `isMultiplicative_charCoeff_tateOp` — TateRiesz.lean:91–116.
  - Source: [LWX] Rmk 3.25: "for n = n^±_k, c_n(T) is equal to T^{λ_n} times a unit in Λ^{>1/p}";
    [LWX] Thm 3.16 (3.16.1): "c_n ∈ T^{λ(n)}·Λ^{>1/p} for n ∈ Z≥0"; [LWX] Step II: convexity
    "λ(n_{k+1} − i) ≥ λ(n_{k+1}) − (k+1)φ(q)i with equality if and only if i ∈ [−t,t]".
  - Lean ↔ source: `IsHaloVertex` = the Rmk 3.25 hypothesis at an index where `λ` has a genuine
    vertex (the increment `⌊(n−1)/t⌋ − ⌊(n−1)/pt⌋ < ⌊n/t⌋ − ⌊n/pt⌋`); dominance at
    `ρ = p^{λ(n) − λ(n−1)}`: `‖c_m‖ρ^m ≤ p^{−λ(m) + s m}` and `λ(m) − λ(n) ≥ s(m − n)` with
    strictness for `m > n` by convexity (`s` = left slope `< ` right slope).
  - Discharged by: `norm_charCoeff_upOp_le` (Halo.lean:124), `lwxLambda_succ`, `monotone_sub_div`
    (Halo.lean:44/49), `lwxLambda_eq_sum_comp`, L-A3 (`isMultiplicative_ofInt_of_isUnit`,
    `isMultiplicative_mul`, `isMultiplicative_T` + `pow`), L-F2.
  - Sizing: source 3 lines; expect ~200 LOC (floor-arithmetic convexity).
  - Attacks: [1] is `n` really the *largest* index attaining the max (strictness for `m > n`)?
    For `m > n`: `λ(m) − λ(n) ≥ (m − n)·(λ(n+1) − λ(n)) > (m−n)s` since the increments are
    nondecreasing and `s < λ(n+1) − λ(n)` by the vertex condition ✓; for `m < n`:
    `λ(n) − λ(m) ≤ (n−m)·(λ(n) − λ(n−1)) = (n−m)s` ✓ (increments `≤` the last one); [2] edge
    `n = 0`: `(n−1)/t = 0/t` in `ℕ`-subtraction — the vertex condition `0 < 0 − 0` is false, so
    `n = 0` is excluded, correct since `c_0 = 1` and `λ(0) = 0 = λ(1)`… (the polygon has no vertex
    at `0`) — worth a docstring note; `t = 1`, `p = 3` sanity: increments `⌊k⌋ − ⌊k/3⌋`: `0,1,2,2,3,…`
    vertices where the increment jumps ✓; [3] `hp2` needed only through `norm_charCoeff_upOp_le`;
    [4] drift: the hypothesis is honestly labelled as [LWX]'s derived fact taken as input;
    [5] discharge names read ✓. SURVIVED.
- **L-F3b** (leaf, project): `HaloInt.isUnit_of_isUnit_coeff_zero`, `UpDatum.isHaloVertex_of_isUnit_coeff`
  — TateRiesz.lean:144, :153 (added at the user's review: the hypothesis must match the form
  [LWX] actually derive).
  - Source: [LWX] Cor 3.18 (verbatim): "we have `v(c_n(T)) ≥ λ(n)v(T)` for every `n ≥ 0`, with
    equality holding if and only if `b_{n,λ(n)} ∈ ℤ_p^×`"; Step II: "`n^−_{k+1}` (resp. `n^+_{k+1}`)
    is the minimal index in `[n_{k+1} − t, n_{k+1}]` (resp. maximal index in `[n_{k+1}, n_{k+1} + t]`)
    such that `b_{n^−_{k+1},λ(n^−_{k+1})}` (resp. `b_{n^+_{k+1},λ(n^+_{k+1})}`) is a `p`-adic unit in
    `ℤ_p`"; Rmk 3.25: "for `n = n^±_k`, `c_n(T)` is equal to `T^{λ_n}` times a unit in `Λ^{>1/p}`";
    Lemma 3.15: "The ideal `𝔪_Λ Λ^{>1/p}` is the same as the principal ideal `(T)`."
  - Lean ↔ source: `hb : IsUnit (charCoeff (D.op ω) n (λ(n)))` is "`b_{n,λ(n)} ∈ ℤ_p^×`" (the
    `T^{λ(n)}`-coefficient of `c_n`); the conclusion `IsHaloVertex` is Rmk 3.25's "`T^{λ_n}` times a
    unit", the step LWX take without comment; the units lemma is that step.
  - Discharged by: `exists_charCoeff_upOp_eq_T_pow_mul` (Halo.lean:137), `HaloInt.coeff_T_pow_mul`
    (HaloRing.lean:461), a coefficientwise `p`-adic Neumann series in `HaloInt` (new, ~150 LOC).
  - Sizing: source 1 line (implicit); expect ~200 LOC.
  - Attacks: [1] is every element with unit constant coefficient a unit? Checked on `1 + pT⁻¹`
    (inverse `∑ (−pT⁻¹)^k`, which lies in `HaloInt` and multiplies correctly) and on `1 + T` (Neumann,
    `‖T‖ < 1`) ✓; a potential counterexample `pT⁻¹` itself has constant coefficient `0` — excluded
    by the hypothesis ✓; [2] edges: `g` constant (`g = b`) ✓; [3] `‖e‖ = 1` in `IsHaloVertex` is
    automatic for units of `HaloInt` (both `e, e⁻¹` have norm `≤ 1`) — the field is redundant but
    harmless; [4] drift: none (the hypothesis is now LWX's own); [5] `exists_charCoeff_upOp_eq_T_pow_mul`
    signature read (Halo.lean:137–145) ✓. SURVIVED.
- **L-F4** (assembly, milestone): `exists_isDominantFactorization_tateOp`,
  `exists_rieszColemanProjection_tateOp` — TateRiesz.lean:118–140.
  - Source: [LWX] Rmk 3.25 ("we can factor Char(P)") and [JN] Thm 2.2.2 applied over `A`; the
    `lwx-halo` plan: "the boundary-annulus base A = Λ^{>1/p}[1/T] is … Tate, and the module is
    ON-able, so [JN]'s hypotheses are satisfied there".
  - Lean ↔ source: assembly of L-E2 (with `ρ` from L-F3), L-E3, L-D1 (`Q := P`, `S := G`,
    `v := leadingCoeff P` unit by `IsDominantPoly`), packaged as `IsRieszColemanProjection`.
  - Conditional on `IsHaloVertex` (Atkin–Lehner/classicality, plan.md "Decision 5"; interface L-F3b).
  - Discharged by: L-E2, L-E3, L-F1–F3, L-D1; one-line anonymous-constructor assembly plus the
    `IsRieszColemanProjection` record (`P.coeff 0 = 1`, `IsEntire G`, `G(0) = 1`, `eq`, `coprime`
    are fields of `IsDominantFactorization` + L-E3).
  - Attacks (composition): [1] could L-E2's `ρ` and L-F3's `ρ` differ? L-F3 *produces* the radius
    used in L-F4's statement ✓ same expression; [2] `IsEntire (charPowerSeries (tateOp))` from
    `charPowerSeries_isEntire` + `isCompactoid_tateOp` ✓ (hypothesis of L-E2); [3] the unit `v`:
    `IsDominantFactorization.dominant.2 : IsUnit P.leadingCoeff` ✓; [4] drift: none;
    [5] every child is a leaf above. SURVIVED.

---

## Confidence gate (Step 5) — status

1. Every leaf discharged from mathlib / project code, or is one of the five reconstructed
   proofs flagged above (L-C5's unit-criterion route, L-D5 Lemma 3.1, L-E3 norm-level Lemma
   2.2.7, L-B4 identity theorem, L-D6's `deg G ≤ n` via localisation) — each reconstructed from
   quoted source statements plus mathlib, with no external unknown.  **No REVIEW-PENDING
   leaves; no `/expert-review` question filed.**
2. Skeleton compiles: `lake build` 2898 jobs, sorries only ✓.
3. Every leaf has a verbatim source quote + Lean ↔ source paragraph ✓ (the three reconstructions
   carry the *statement* quotes and are labelled).
4. Attacks blocks: present for every leaf and for the internal nodes L-D6, L-F4 ✓; all SURVIVED,
   with one execution-time tightening recorded (L-E1's multiplicativity hypothesis on `.mul`).
5. Prior-B2 log consulted; two shape matches addressed (transpose design; radius/characteristic
   hypotheses) ✓.
6. Tree mirrors the sources: T5 follows [Bel] II.2.18 → II.2.15/II.2.16/II.2.17 with [Buz07]
   3.2/3.3 for the refinements; T4 follows [Bel] §II.2.4; T6 follows [Bel] II.3.6; every LOC
   estimate cites its source line count ✓.
7. Single-conclusion: see "Statement-shape check" above ✓.

**Feasibility.** Every tranche is discharged from existing infrastructure plus the leaves above;
the two heavy leaves are L-C3/L-C4 (Coleman's `D` on entire series, ~750 LOC) and L-D6 (Buzzard's
rank argument through localisation, ~900 LOC).  Total estimate ≈ 6,000 LOC over 7 files — a
board of the size of `lwx-halo`.  The proposal's fourth item ([JN] §2.3) and the Gelfand-spectrum
form of 2.2.13 are out of scope by design (plan §Goal).
