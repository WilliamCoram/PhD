# Development Plan: LWX halo estimate (Tier 1)

**BOARD PATH: `.mathlib-quality/lwx-halo/`** — named board; the default `.mathlib-quality/`
root belongs to the (completed) NewtonPolygons project and must not be touched. Every
`/beastmode` invocation for this project must name this path.

Planned 2026-09-02. Source: Liu–Wan–Xiao, *The eigencurve over the boundary of weight
space* (arXiv:1412.2584v4; the November 2016 version — page/section numbers below refer
to it; a copy is in the user's possession, cite as [LWX]). Secondary: Johansson–Newton
arXiv:1604.07739 (Tier-2 reference only).

## Goal

The unconditional core of [LWX] — Theorem 3.16 and Corollary 3.18 — for a `U_p`-shaped
integral operator with class-set block structure, at an odd prime `p`, one weight disc at
a time:

1. **Theorem 3.16 (the halo estimate).** For the integral `U_p`-matrix `P` over
   `Λ^{>1/p}` built from a `t`-block coset datum with local matrices
   `δ ∈ (pℤ_p, ℤ_p; pℤ_p, ℤ_p^×)`, the characteristic power series
   `Char(P) = Σ c_n Xⁿ` is well defined and
   `‖c_n‖ ≤ ‖T‖^{λ(n)}` — equivalently `c_n ∈ T^{λ(n)}·Λ^{>1/p}`, equivalently
   coefficientwise `v_p(b_{n,m}) ≥ max(λ(n) − m, 0)` for `c_n = Σ_m b_{n,m}T^m` —
   where `λ(n) = Σ_{k<n} (⌊k/t⌋ − ⌊k/pt⌋)`.
2. **Corollary 3.18 (lower-bound polygon at every halo weight).** For every `T₀` in a
   complete ultrametric field with `p⁻¹ < ‖T₀‖ < 1`, the Newton polygon of the
   specialized series `Σ_n (Σ_m b_{n,m}T₀^m) Xⁿ` lies on or above
   `NewtonPolygon₀.ofSlopes (fun k => (⌊k/t⌋ − ⌊k/pt⌋)·v(T₀))`.
3. **Quaternionic instantiation (Prop 3.1's shape).** The local Iwahori coset data for
   `Iw_q (p 0; 0 1) Iw_q` produces matrices of the required shape, so the quaternionic
   double-coset recipe (`heckeOperatorSlash_apply_rep`) yields a valid `UpDatum` at any
   class set.
4. **The integral model `S^D_int` and the Hecke seam (tranche H, added 2026-09-03).**
   The universal character, the monoid `M₁`, the action [LWX, (2.3.2)] on
   `C(ℤ_p, Λ^{>1/p})`, the rescaled model [LWX, (5.4.1)] as `c(ℕ, Λ^{>1/p})`, the
   integral space as an instance of the repo's **ring-generic** `QMF/Slash/` layer
   (verified: `AutomorphicFunction`, `RightSlashAction`, `slashFixedPointsOfLE`,
   `heckeOperatorSlash`, `heckeOperatorSlash_apply_rep`, `bijective_evalAtRepsSlash`
   all run over an arbitrary `Semiring R` — Slash/HeckeMonoid.lean:47–50,
   Slash/HeckeMatrix.lean:35,181), and the seam theorem `intEvalAtReps_comm`: any
   operator satisfying Prop 3.1's display intertwines with `UpDatum.op`, so
   [LWX, Prop 3.4] becomes a theorem (`cfunSlash_mahlerEmbed`) and Theorems 3.16/
   Cor 3.18 apply to the genuine `[UηU]` on `S^D_int`.

**Out of scope (recorded so nobody re-litigates):** the touching hypothesis and Theorem
1.3's component decomposition; §4's Claim and Theorem 1.5; Atkin–Lehner; classicality;
Hida theory; JN §2.2 ring-level Riesz; `p = 2` (`q = 4`); the comparison of the
integral model's `Char` with `QMF.Weight.heckeCharPowerSeries` at each specialized
weight (LWX Prop 2.17 — a Mahler-basis ↔ analytic-disc-basis change; the one remaining
model seam); supplying a *concrete* quaternion algebra/level instance of the coset data
(fork-style application, mechanical given `QMF` finiteness + `heckeOperatorSlash_apply_rep`).

## Architecture (D′ — a planning-time simplification of the agreed D)

The conversation's architecture (D) planned a Tate ring `A = Λ^{>1/p}[1/T]` so the
Banach–Tate Fredholm library applies verbatim. Planning verification improved this:

- **No `A`, no `IsTate` needed for Tier 1.** `TateFredholm`'s *definitions*
  (`matrixCoeff`, `minor`, `charCoeff`, `charPowerSeries`) are norm-free and already
  stated over any `NormedCommRing`; only the theorems carry `[IsTate]`. Tier 1 adds one
  general theorem (two-sided-weight bound, no `IsTate`) instead of transposing the
  library. The reason `A` is unnecessary: LWX's diagonal conjugation
  `P' = D P D⁻¹` (which forces `T⁻¹`) acts trivially on *principal minors* — for any
  permutation `π` of a finite index set `S`, `Σ_{a∈S} w'(π a) = Σ_{a∈S} w'(a)` — so the
  Hadamard bound with the two-sided weight `max(w(row) − w'(col), 0)` gives
  `‖minor S‖ ≤ σ^{Σ_S w − Σ_S w'}` directly over the *integral* ring. This is the same
  computation as [LWX] proof of Thm 3.16, read at the minor level.
- **No operator-level base change for Cor 3.18.** `ev_{T₀} : Λ^{>1/p} → K` is
  power-bounded, not bounded (`‖Tⁿ‖ = p^{−n}` but `‖T₀ⁿ‖ = ‖T₀‖ⁿ`), so
  `charPowerSeries_baseChange` does not apply — and is not needed: Cor 3.18 is proved in
  [LWX] by the coefficient computation
  `v(b_{n,m}T₀^m) ≥ max(λ(n)−m,0) + m·v(T₀) ≥ λ(n)·v(T₀)`, which we transcribe.
- The Tate ring `A` (with `T` inverted) remains the natural Tier-2 home (JN Thm 2.2.2
  needs Noetherian Tate + (Pr)); building it is deferred to that board.

## Key design decisions

1. **Per-ω from the start.** Fix a character `ω : (ZMod q)ˣ →* ℤ_[p]ˣ` of the torsion
   part; the coefficient ring is the `ω`-component `Λ_ω^{>1/p}`, concretely `HaloInt p`
   below. ([LWX] does exactly this at the top of §3: "we fix a character ω of Δ".)
   No group algebra `ℤ_p[Δ]` is built.
2. **`p` odd (`q = p`).** [LWX] handles `p = 2` with `q = 4` by parallel arguments
   (their Lemma 3.13 case (d)); we take `p` odd, `Fact (p.Prime)` + `p ≠ 2` where the
   estimate `v(q) = 1` is used. Recorded as a hypothesis, not baked into definitions
   where avoidable.
3. **The ring is concrete.** `HaloInt p` := functions `d : ℤ → ℤ_[p]` with
   `‖d j‖ ≤ p^{min(0,j)}` (i.e. `v(d_j) ≥ max(0, −j)`; the exact [LWX] description of
   `Λ^{>1/p} = ℤ_pJT, pT⁻¹K` unpacked — their Cor 3.18 proof: "if `Σ d_m T^m ∈ Λ^{>1/p}`
   then `v(d_m) ≥ max(0, −m)`"). Convolution product (a `tsum` over ℤ; summability from
   the coefficient bounds via `TateFredholm.summable_of_tendsto_cofinite`), norm
   `‖d‖ = ⨆ j, ‖d j‖·(p:ℝ)^{−j}` (values in [0,1]; makes `ℤ_[p] → HaloInt p` isometric
   and `‖T·x‖ = p⁻¹‖x‖` an exact shift identity). `𝔪^k`-membership is the norm bound:
   `‖x‖ ≤ p^{−k} ↔ ∀ j, v(x_j) ≥ max(k − j, 0) ↔ x ∈ Tᵏ·HaloInt` (Lemma 3.15's
   content, coefficientwise).
4. **Entries are coefficient streams, not `PowerSeries`.** The matrix entry
   `P_{m,n}(δ)` is *defined* by its `T`-coefficient stream
   `r ↦ ω-unit · Δ̃^m (choose(f_δ, n) · choose(g_δ, r))(0)` ([LWX] (3.4.1) expanded per
   the Prop 3.14 proof display), directly a `HaloInt p` element supported in `ℕ`. All
   `𝔪`-power statements are coefficientwise valuation bounds; no ideal-power API.
5. **Mahler calculus on `C(ℤ_[p], ℤ_[p])`** reusing mathlib: `Δ̃ = fwdDiff 1`
   (with `fwdDiff_iter_eq_sum_shift` = [LWX] (3.3.1)), `mahler k = Ring.choose · k`
   (`BinomialRing ℤ_[p]` instance exists), `mahlerEquiv`/`mahlerSeries` for expansions,
   Chu–Vandermonde `Ring.add_choose_eq` for [LWX] (3.5.3). New: the Leibniz rule
   (3.5.1), `fwdDiff`-of-`mahler` (3.5.2), tilted degree (Def-Prop 3.8, defined by
   clause (2): `∀ j, ‖Δ̃^j f 0‖ ≤ p^{n−j}`), and Lemmas 3.7, 3.10–3.13.
6. **The `p`-adic logarithm is defined by its series and used only through three
   lemmas** (integrality of `ℓ(u)` for `u ∈ 1 + pℤ_p`; additivity; the coefficient
   shape of `z ↦ ℓ(1 + xz)` for `v(x) ≥ 1`). Additivity is genuinely needed (the
   Prop 3.14 proof splits `g(z) = ℓ⟨d⟩ + ℓ(1 + (c/d)z)`; the direct composite estimate
   provably loses `v(k)` at `k = p^m` and does not recover Lemma 3.13's shape — checked
   at planning time). Teichmüller lift `ωT(x) = lim x^{pⁿ}` is a small self-contained
   API gap (AG1).
7. **The operator is abstracted as `UpDatum`**: a `t`-indexed family of targets and
   local matrices `δ i j ∈ M₂(ℤ_p)`, `p` summands per block-row, each
   `δ ∈ (pℤ_p, ℤ_p; pℤ_p, ℤ_p^×)` ([LWX] Prop 3.1(1)(3); property (2), `p` per
   *column*, is not used by Thm 3.16 and is omitted). The quaternionic side supplies an
   instance; the estimate is proved for any datum.
7′. **(2026-09-03 revision) `LocalMat` is `M₁`-first.** `LocalMat` is [LWX, (2.3.3)]'s
   `M₁` in record form (`p | c`, `d` a unit; `a` free), with the `U_p`-shape
   (`a ∈ pℤ_p`) as the refinement `IsUpShape`, and **both** cases of [LWX, Prop 3.14]
   are stated: case (1) (`norm_entry_le`, exponent `m − ⌊n/p⌋`, under `IsUpShape`)
   feeds the halo estimate; case (2) (`norm_entry_le_M1`, exponent `m − n`, any
   `δ ∈ M₁`) feeds the stability of the rescaled model ([LWX, §5.4]'s claim) — a
   planning-time finding: tranche H is impossible with case (1) alone.
7″. **Tranche H reuses the ring-generic slash layer** (goal item 4): the cocycle is
   proved once, on the *function* model `C(ℤ_p, Λ^{>1/p})` where it is Möbius
   composition + `univChar_mul`; the sequence model `c(ℕ, Λ^{>1/p})` receives the
   action through `mahlerEmbed` (`a ↦ ∑ aₙTⁿ·binom(z,n)`), whose injectivity and
   coefficient extraction use only iterated forward differences (`binom(0,k) = δ_{k0}`)
   — **no Mahler expansion theorem over `Λ^{>1/p}` is needed anywhere**. The `M₁` ↔
   `QMF.Sigma0'` identification (same carrier; `Sigma0'` wants a `Valued` field
   instance on `ℚ_[p]`) is optional polish, recorded in ticket H2.
8. **Statements are single-conclusion**; the polygon corollary reuses
   `NewtonPolygon₀.ofSlopes` + `IsBelow` exactly as
   `QMF.Weight.isBelow_newtonPolygon_heckeCharPowerSeries` does (same anchoring at the
   origin via `c₀ = 1`).

## Mathlib/project inventory (verified at planning time)

| Concept | Status | Action |
|---|---|---|
| `fwdDiff`, `Δ_[1]`, `fwdDiff_iter_eq_sum_shift`, `shift_eq_sum_fwdDiff_iter` | `Mathlib.Algebra.Group.ForwardDiff` (verified by grep) | USE |
| `mahler k`, `mahler_apply` (= `Ring.choose`), `PadicInt.instBinomialRing`, `continuous_choose`, `mahlerSeries`, `hasSum_mahlerSeries`, `mahlerEquiv(_apply)`, `fwdDiff_mahlerSeries` | `Mathlib.NumberTheory.Padics.MahlerBasis` (verified) | USE |
| Chu–Vandermonde for binomial rings (`add_choose_eq`, per file header) | `Mathlib.RingTheory.Binomial` (verified header line 49) | USE for (3.5.3); exact name to pin at skeleton time |
| `PadicInt.norm_le_pow_iff_mem_span_pow`, `norm_le_one` | `Mathlib.NumberTheory.Padics.PadicIntegers` (verified) | USE |
| `summable_mul_of_summable_norm`, `tsum_mul_tsum_of_summable_norm` (general index) | `Mathlib.Analysis.Normed.Ring.InfiniteSum` (verified) | USE for `HaloInt` ring axioms |
| `TateFredholm.summable_of_tendsto_cofinite`, `norm_tsum_le_iSup` | `PhD/TateFredholm/Tate.lean` (verified) | USE |
| `TateFredholm.matrixCoeff/minor/charCoeff/charPowerSeries` (norm-free defs) | `PhD/TateFredholm/{Matrix,Fredholm}.lean` (verified) | USE unchanged |
| operator-from-bounded-matrix (`exists_coeffEquiv` area) | `PhD/TateFredholm/Matrix.lean` (README §5) | USE; pin exact recovery statement at skeleton time |
| `choose_two_le_sum`, `sum_div_le_sum_block` proof pattern | `PhD/TateFredholm/Slopes.lean` (verified) | MIRROR for the monotone-weight min lemma (statement subsumes both; existing lemmas untouched) |
| `NewtonPolygon₀.ofSlopes`, `isNewtonPolygonOf_ofSlopes`, `IsBelow`, `coeffVal`, `newtonPolygon₀OfPowerSeries` | `PhD/NewtonPolygons/{OfSlopes,CoeffVal}.lean` (verified) | USE; mirror `isBelow_newtonPolygon_heckeCharPowerSeries`'s assembly |
| `AbstractHeckeOperatorSlash.heckeOperatorSlash_apply_rep` | `PhD/QMF/Slash/HeckeMatrix.lean:57` (verified) | CITE as the double-coset mechanism for the instantiation tranche |
| Iwahori η-decomposition pattern (`uₜ`, `vₜ = η uₜ`) | `PhD/JacobsSlash/U3/3_EtaDecomposition.lean` (p=3 instance) | MIRROR at general odd `p` |
| p-adic exp/log | NOT in mathlib; fork has `padicExp/padicLog` at `‖3‖`-generality | DEFINE `logQ` fresh at odd `p` (three lemmas only; fork's proofs are the pattern) |
| Teichmüller lift on `ℤ_[p]ˣ` | NOT found in mathlib (`WittVector.teichmuller` is a different animal) | AG1: define via `x ↦ lim x^{pⁿ}` |
| Λ / Iwasawa algebra / `ℤ_pJT, pT⁻¹K` | NOT in mathlib, not in repo | DEFINE `HaloInt p` (design decision 3) |

## File structure (all new files; no existing file is edited)

```
PhD/LWX/HaloRing.lean       — HaloInt p: carrier, ring, norm, completeness, T, coeff API,
                              specialization lemma (coefficient-level)
PhD/LWX/UnitsLog.lean       — AG1: Teichmüller ωT, ⟨·⟩; logQ series + 3 lemmas
PhD/LWX/TiltedDegree.lean   — Δ̃-calculus add-ons (3.5.1)–(3.5.4), polynomial degree
                              (Def 3.6/Lemma 3.7), tilted degree (Def-Prop 3.8, Lemmas
                              3.10–3.13), limit-closure
PhD/TateFredholm/TwoSidedBound.lean — general charCoeff bound: summability + Hadamard for
                              two-sided weights over complete ultrametric NormedCommRing
                              (no IsTate); monotone-weight initial-segment min lemma
PhD/LWX/UpMatrix.lean       — UpDatum; the entry stream (Prop 3.4 shape); Prop 3.14
                              bounds; the CLM on c(ι × ℕ, HaloInt p)
PhD/LWX/Halo.lean           — λ and its floor identities; THEOREM 3.16; COROLLARY 3.18;
                              local Iwahori decomposition + δ-shape; quaternionic UpDatum
PhD/LWX/IntegralModel.lean  — tranche H (2026-09-03): universal character, M₁, the
                              (2.3.2) action on C(ℤ_p, Λ^{>1/p}), mahlerEmbed (5.4.1),
                              S^D_int via the ring-generic QMF/Slash layer, the seam
                              intEvalAtReps_comm
```

Namespace: `LWX`. Import spine: HaloRing ← (UnitsLog, TiltedDegree indep.) ← UpMatrix ←
{Halo, IntegralModel}; TwoSidedBound only imports TateFredholm.Fredholm; IntegralModel
also imports PhD.QMF.Slash.HeckeMatrix.

## Dependency graph (tranche level)

```
A (HaloRing)  ────────────────┐
B (UnitsLog)  ──┐             ├──► D (UpMatrix) ──► F (Halo: Thm 3.16, Cor 3.18)
C (TiltedDegree)┴─────────────┘         │              ▲
E (TwoSidedBound, independent) ─────────┼──────────────┘
G (quaternionic shape, independent)     └──► H (IntegralModel: S^D_int, the seam)
B ──────────────────────────────────────────► H
```

Parallel capacity at start: A ∥ B ∥ C ∥ E ∥ G-local (5 workers); H joins after A/B/D
fronts open.

## Generality decisions

- Weights/bounds phrased with `‖·‖ ≤ (p:ℝ)^{−k}` (real exponents via `zpow`), not
  `Ideal.pow` membership — coefficientwise statements are the workhorse everywhere.
- The two-sided bound theorem in E is stated for an arbitrary index `I`, arbitrary
  weights `w w' : I → ℕ`, any complete ultrametric `NormedCommRing R` with
  `NormOneClass` — strictly more general than both the existing row bound and the LWX
  application; the existing `norm_charCoeff_le_pow` becomes derivable but is left
  untouched.
- `UpDatum` is level- and quaternion-free; the class set enters only as `Fintype ι`.
- `logQ`/`ωT` at odd `p` only (`q = p`); the `p = 2` variants are out of scope.

## Deferred seams and THE TWO FUTURE BOARDS (revised 2026-09-03)

Tranche H absorbed the former deferrals "build `S^D_int`/Prop 3.4 as a theorem" and
"the adelic half of Prop 3.1" (the seam is now `intEvalAtReps_comm`, with the display
hypothesis discharged by the already-proved ring-generic
`heckeOperatorSlash_apply_rep`). What remains, in three bins:

**Future board 1 — `lwx-slopes` (coefficient-level Tier 2; plan after this board's
milestones land).** Needs *nothing* beyond this board's outputs — no Tate ring, no
Riesz, no rigid geometry:
- Cor 3.18's sharpness clause (equality iff `b_{n,λ(n)} ∈ ℤ_p^×`; the
  `min(v(T), 1−v(T))` margins);
- LWX Lemma 4.1 (upper/lower polygon gap `(p²−1)t·v(T)/8`);
- §4.2's Claim (slope ratios independent of `T₀` near the boundary);
- Thm 1.3 Step II's vertex analysis and the `X_I` slope statement, and Thm 1.5's
  first half (`αᵢ(ω)` sequence) — both **conditional on a touching hypothesis**
  (standing in for Atkin–Lehner + classicality, the `hClassNumberOne` pattern).

**Future board 2 — `tate-riesz` (JN §2.2–2.3): DONE 2026-09-06**, board
`.mathlib-quality/tate-riesz/`.  Delivered: the Tate ring `A = HaloInt[1/T]` with `IsTate`
(`PhD/LWX/HaloTate.lean`); JN Thm 2.2.2 ring-level Riesz **without any Noetherian
hypothesis** (`PhD/TateFredholm/RieszColeman.lean`, on top of `Entire`/`Resultant`/
`Coleman`/`Charpoly`) with the rank, the determinant splitting, `Ker Q*(u) = range (1 − p)`,
uniqueness of the complement and JN 2.2.13's decomposition core; the norm-level vertex
factorisation `F = P·G` with relatively prime factors (`PhD/TateFredholm/SlopeFactor.lean`);
and the application to the halo `U_p` at a vertex (`PhD/LWX/TateRiesz.lean`, LWX Rmk 3.25
for one vertex, conditional on `IsHaloVertex` — the Atkin–Lehner/classicality input, with
`isHaloVertex_of_isUnit_coeff` as the interface).  Still open: JN's Gelfand-spectrum form of
the slope conditions, JN §2.3 spectral varieties, and the full product factorisation
`Char = P₀·P₍₀,₁₎·P₁·⋯` over all vertices.

**Still deferred with no board (research-scale or cosmetic):**
1. LWX Prop 2.17 — the Mahler ↔ analytic-disc comparison of `ev_{T₀}(Char)` with
   `QMF.Weight.heckeCharPowerSeries` (Colmez's rescaled basis; genuinely non-diagonal).
   **DONE at `m = 1` by the `lwx-seam` board (2026-09-05):** `PhD/LWX/Seam.lean`
   (`specCharSeries_ofCerts_eq_heckeCharPowerSeries`) on the sub-annulus `p⁻¹ < ‖T₀‖`,
   `‖T₀‖² < p⁻¹`; the Colmez basis change is `PhD/LWX/Colmez.lean`, the halo weight
   `PhD/LWX/HaloWeight.lean`.
2. Atkin–Lehner (Prop 3.22), classicality (Prop 2.15), Hida (Thm 3.19/Cor 3.21),
   theta/BGG degrees — enter `lwx-slopes` only as hypotheses.
3. A *concrete* quaternion algebra/level instance of the coset data (fork-style
   application of `heckeOperatorSlash_apply_rep` + QMF finiteness).
   **DONE by the `lwx-seam` board (2026-09-05):** `PhD/LWX/Certificates.lean` (Prop 3.1 in full
   for the genuine `[UηU]`, `(2.11.1)` at a neat level) and `PhD/LWX/Quaternionic.lean`
   (`D/ℚ` at the place `(p)` via `Padic.adicCompletionEquiv`, Prop 2.17 and the spectral
   reading `evalT_specCharSeries_eq_zero_iff`).
4. `p = 2`; the full `ℤ_p[Δ]` factor; the `M₁` ↔ `Sigma0'` identification.

## ChatGPT validation

Skipped: the `chatgpt-math` MCP server failed to connect this session (cached failure).
To be run at the user's discretion before execution if desired.
