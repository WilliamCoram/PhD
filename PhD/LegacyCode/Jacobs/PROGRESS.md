# Jacobs formalisation — project progress

> **LEGACY (moved to `PhD/LegacyCode/` on 2026-08-21).**  Frozen history of the
> left-action original; do not develop or import from here.  The live replacement is
> the right-slash fork `PhD/JacobsSlash/` (see its `PROGRESS.md`).  The status below
> is preserved as written and is no longer maintained.

Status as of **2026-08-06**.  Boards: Tranche A / AG-NP / AG-W on
`.mathlib-quality/jacobs/` (COMPLETE), AG-B on `.mathlib-quality/qmf/` (COMPLETE except
cleanup tail), endgame refactor on `.mathlib-quality/jacobs-endgame/` (ALL PROOF WORK
DONE 2026-08-06; consolidated cleanup wave in progress).  The default
`.mathlib-quality/` board belongs to the NewtonPolygons instance — never touch it from
Jacobs work.

## 1. The result chain

Everything in [Jacobs, *Slopes of Compact Hecke Operators*, Ch. 2 §2.1] is proved on
standard axioms, in five composable layers:

1. **Serre/Fredholm theory** (`PhD/TateFredholm/`): `det(1 − Tu)` for compactoid
   operators, trace property, Riesz eigenvalue theory.
2. **The matrix results** (Tranche A + AG-W): the transcribed operators satisfy
   Lemmas 2.7–2.15, Thm 2.12/2.14, Cor 2.16, and
   `det(1 − T·U3MatrixOp) = ∏ₜ det(1 − T·M_{t,t})`.
3. **The slope reading** (AG-NP): the valuation points `(m, m²/2)` really give Newton
   polygon slopes `1/2, 3/2, 5/2, …`.
4. **The identification** (AG-B): the genuine Hecke operator `U₃ = [U₁(9)η₃U₁(9)]` on
   `L(U₁(9), A₃)` has the certificate block matrix, whose Fredholm determinant equals
   `charPS(U3MatrixOp)` on the nose (determinant-twist bridge).
5. **The endgame** (PROVED 2026-08-06; cleanup wave remaining): `det(1 − T·U₃)` is the
   object `charPowerSeriesU3` (= `charPS(U3MatrixOp)` by `charPowerSeriesU3_eq_U3MatrixOp`);
   the model iso `kappaFormsModelEquiv` and transport `evalU3_heckeU3` justify the name;
   `charPowerSeriesU3_factorisation` gives the eigenblock factorisation over every
   isometric `L ∋ ω`, witnessed at `L₃ = ℚ₃(ζ₃)` — with the proved `M₂,₂`-factor slope
   reading, [Jac Cor 2.16] is a theorem about `U₃`.

Single external debt: `hClassNumberOne` ([Jac Lemma 1.22], FLT interface, contracted
permanent `sorry`; every consumer takes `hcn` as an explicit hypothesis).

## 2. File inventory

### Analytic / operator layer (abstract `K`: complete ultrametric, `CharZero`)

| File | Contains / proves |
|---|---|
| `PadicAnalytic.lean` | `padicLog`, `padicExp`, `unitPow`, `binomialCoeff`; convergence and norm bounds on the discs; `padicExp_add`, `padicExp_padicLog`, `padicLog_mul` (Iwasawa-limit route); residue-char-3 norm lemmas (`norm_natCast_eq_pow_padicValNat`, `sq_norm_factorial_ge`).  Sorry-free.  [Kob84 Ch. IV] facts behind [Jac pp. 29, 38–39]. |
| `GenFun.lean` | matrices ↔ generating functions ↔ operators on `c(ℕ,K)`: `idx`, `ofCoeffs`/`ofGenFun` + `matrixCoeff_ofCoeffs`, `hyps_of_row_decay`, `diagRescale` calculus (`diagRescale_mul`, …), `diagOp` + `matrixCoeff_diagOp_comp`, `isCompactoid_of_row_decay`.  Sorry-free.  [Jac §1.1 Prop 1.3, §1.2 Prop 1.7, Cor 1.10]. |
| `BinomialTheorem.lean` | the `p`-adic binomial theorem `∑ₙ (t choose n) zⁿ = unitPow t (1+z)` (density-in-exponent proof).  Sorry-free.  [Jac p. 29 display]. |
| `BaseChange.lean` | `TateFredholm.charCoeff_map`/`charPowerSeries_map` (Fredholm determinant base change along isometric ring homs), `MvPowerSeries.map_inv₀`, map-compatibility of the analytic layer (`map_padicLog/Exp/binomialCoeff/unitPow`) and of `kappaSeries₂`/`linSeries`/`quadSeries`/`weightGenFun`/the six `h`'s.  Sorry-free (2026-08-06). |

### Slopes layer (Tranche A + AG-NP, abstract `K` with `(t, ν, ω)`)

| File | Contains / proves |
|---|---|
| `SlopeTheorem.lean` | **[Jac Thm 2.12]** abstract slope theorem: `norm_charCoeff_of_unit_minors`, `val_charCoeff_of_unit_minors`; `ϖ₃` (`3` as `PseudoUniformizer`); determinant valuation lemmas.  Sorry-free. |
| `U3Data.lean` | the nine transcribed `ε`-matrices (`eps01M1` … `eps21M`; erratum E1 corrected), `weightGenFun` ([Jac Prop 2.6] formula), `h01`–`h21` ((2.1.4)–(2.1.9)), **[Jac Lemma 2.7]** quantitative integrality (`norm_coeff_h02_le`, `norm_coeff_h12_le`, `RowInt` tower), **[Jac Lemma 2.11]** (`lemma211_first/first'/second/second'`), rescale calculus (`diagRescale_weightGenFun`, `weightGenFun_smul`), `M22genFun`/`M22op`/`isCompactoid_M22op`.  Sorry-free. |
| `Slopes.lean` | ω-arithmetic (`sq_two_omega_add_one`, `norm_omega`); **[Jac Thm 2.14]** (`norm_coeff_NgenFun_sub_negGeom_lt`); **[Jac Lemma 2.13]** (`norm_coeff_NgenFun_le`); **[Jac Cor 2.15]** (`norm_det_NgenFun_minor`); trace-conjugation step (`M22half`, `charCoeff_conj_eq`, `charCoeff_M22op_eq`); **[Jac Cor 2.16] vertex data** (`sq_norm_charCoeff_M22op`, `val_charCoeff_M22op`); `ext_matrixCoeff`.  Sorry-free. |
| `SlopeReading.lean` | AG-NP: `NewtonPolygon₀.ofSlopes` + spec theorem `isNewtonPolygonOf_ofSlopes`; transports; case A ([Jac Thm 2.12] slopes `0,1,2,…`) and case B ([Jac Cor 2.16] slopes `1/2,3/2,…`: `isNewtonPolygonOf_val_charCoeff_M22op`, `unitSlope_newtonPolygon₀OfPowerSeries_M22op`).  Sorry-free. |
| `Instance.lean` | non-vacuity certificate over `ℂ₃` (`ℂ_[3]`): parameters exist (`exists_omega`, `exists_sqrt_neg_two_near` — no Hensel needed) and the case-B headline instantiates (`slopes_nonvacuous`).  Sorry-free. |

### Block / eigen layer (AG-W)

| File | Contains / proves |
|---|---|
| `BlockOp.lean` | TateFredholm-generality block machinery: `inclSubtype`/`projSubtype`/`restrictOp`/`reindexOp`, `blockIncl`/`blockProj`/`blockOp`/`blockCorner`, `charPowerSeries_reindexOp`, **[Jac Lemma 1.15] = [Ser62 Lemme 2]** (`charPowerSeries_partition`), `charPowerSeries_blockDiag`, coboundary invariance `charPowerSeries_blockOp_twist`.  Sorry-free. |
| `DiamondW.lean` | remaining **[Jac Lemma 2.7]** integrality (`norm_coeff_h01/h10/h20/h21_le`), the six `epsOp**` + compactoids, `U3MatrixOp` + `isCompactoid_U3MatrixOp`, the `δ`-blocks and `Wop` with **[Jac Rem 2.8.2]** `Wop_cube` (`W³ = 1`), `Bop`/`Binvop` + both inverse relations, **[Jac Lemma 2.10]** (`lemma210`: `B⁻¹AB` block-diagonal), `M11op`/`M33op`, **milestone** `charPowerSeries_U3MatrixOp` (`det(1−T·A) = ∏ det(1−T·M_{t,t})`), `charPowerSeries_twist_U3MatrixOp`.  Sorry-free. |

### Adelic layer (AG-B, concrete `K₃` = `v₃`-adic completion of `ℚ`)

| File | Contains / proves |
|---|---|
| `U3/Setting.lean` | `D = ℍ[ℚ]`, `v₃`, `K₃`, `ν₃` (`sq_ν₃`, `ν₃_near`), the splitting `θ₃` (`theta_tmul_one`), `Σ₀`/`Σ₁(9)`, `norm_three_lt_one`.  Sorry-free. |
| `U3/Hurwitz.lean` | the Hurwitz order and its 24 units.  Sorry-free. |
| `U3/Level.lean` | local orders, `U₀(1)`, `U₁(9)`, `D^× ∩ U₀(1) = 𝓞_D^×`; `HClassNumberOne` + `hClassNumberOne` (**the contracted `sorry`**, [Jac Lemma 1.22]). |
| `U3/ClassSet.lean` | **[Jac Thm 2.1]** (`classRep_complete`, `exists_classRep_factorisation`, `exists_classRep_section`) and **[Jac Lemma 2.2]** (`stabilizerAt_classRep`, unconditional).  Sorry-free. |
| `U3/EtaDecomposition.lean` | **[Jac Lemma 2.3]** (`bijOn_etaRep`: `U₁(9)η₃U₁(9) = ⊔ₜ wₜU₁(9)`).  Sorry-free. |
| `U3/KappaAction.lean` | the weight-`κ` action `kappaOp`, **[Jac Prop 2.6]** by design (`matrixCoeff_kappaOp`), **[Jac Def 1.27]**'s action law (`kappaOp_mul`, via `compAn` + ODE + binomial theorem), `kappaModuleAction`.  Sorry-free. |
| `U3/Compose.lean` | analytic substitution `compAn` (ring hom, chain rule, ODE transport, `eq_of_ode`) — the machinery behind `kappaOp_mul`.  Sorry-free. |
| `U3/Factorisations.lean` | **[Jac Lemmas 2.4/2.5 + §B.1]**: the nine certificates (`sigmaTable`/`dTable`/`uTable`/`factorisation`, recomputed by `U3/certificate_search.py`), `classDet`, `epsTable`, matrix-level `adjParams_toMatrix_eq_smul_epsTable`, series-level `sum_weightGenFun_eq_h` (with the determinant-twist scalar).  Sorry-free. |
| `U3/Matrix.lean` | the meeting point: `levelMonoid1`, **[Jac Def 1.30]** `kappaForms` (= `L(U₁(9), A₃)`), **[Jac Def 1.32]** `heckeU3`, certificate `blockOp` + `matrixCoeff_blockOp` (twist-honest), `classWeight`/`twist_factor`/`blockOp_eq_smul_epsOp`, **the AG-B↔AG-W bridge** `charPowerSeries_blockOp_eq_U3MatrixOp`, **the unconditional headline** `heckeU3_apply_classRep`, and `eval_classRep_injective` (under `hcn`).  Sorry-free (except through `hClassNumberOne` in the `'`-form). |
| `U3/Fredholm.lean` | `evalU3` + `bijective_evalU3` ([Buz07 §9] iso at the Jacobs data) + `kappaFormsModelEquiv` (under `hcn`), unconditional transport `evalU3_heckeU3`, `isCompactoid_blockOpU3`, and `charPowerSeriesU3` = **`det(1 − T·U₃)`** with `charPowerSeriesU3_eq_U3MatrixOp`.  Sorry-free (2026-08-06). |
| `U3/HeckeSlopes.lean` | hypothesis transports along isometric `f : K₃ →+* L`; `map_charPowerSeriesU3`; **milestone** `charPowerSeriesU3_factorisation` (`det(1−T·U₃) = ∏ det(1−T·M_{t,t})` over any admissible `L ∋ ω`, `hcn`-free); the concrete witness `L₃ = CyclotomicField 3 K₃` with spectral-norm instances and `charPowerSeriesU3_factorisation_L₃`.  Sorry-free (2026-08-06). |
| `U3/ClassNumberOneFallback.lean` | unimported skeleton of the in-repo [Voight] route to class number one (deferred to FLT). |

### Infrastructure outside `PhD/Jacobs/`

- `PhD/TateFredholm/` — [Ser62] / [Jac §1.2]: `charCoeff`/`charPowerSeries`
  (`Fredholm.lean`), **[Jac Prop 1.14]** trace property (`charPowerSeries_comm`),
  `matrixCoeff`/`IsCompactoid`/`rowNorm` (`Matrix.lean`), `IsTate`/`PseudoUniformizer`
  (`Tate.lean`), Riesz eigenvalue theory (`Riesz.lean`, tatefredholm-eigen board).
- `PhD/QMF/` — abstract automorphic machinery: `AutomorphicFunction`,
  `levelSubmodule`, `heckeOperator`, `heckeOperator_apply_rep` (`HeckeMatrix.lean`),
  `evalAtReps` + `bijective_evalAtReps` (`Decomposition.lean`) — the [Buz07 §9]
  isomorphism `L(U,A) ≅ ∏ A^{Γ_λ}`.
- `PhD/NewtonPolygons/` — the Newton-polygon spec/construction the slope reading
  consumes (parallel board; stable API).

## 3. Where each thesis result lives

| [Jacobs] result | Lean | File | Status |
|---|---|---|---|
| Prop 1.3 (rescale gen. fun.) | `diagRescale` calculus, `matrixCoeff_diagOp_comp` | `GenFun.lean` | proved |
| Prop 1.7 (= Ser62 Prop 3) | `ofCoeffs`, `matrixCoeff_ofCoeffs` (∃-form `TateFredholm.exists_coeffEquiv`) | `GenFun.lean` | proved |
| Cor 1.10 (compactness criterion) | `isCompactoid_of_row_decay` | `GenFun.lean` | proved |
| Prop 1.14 (trace property) | `TateFredholm.charPowerSeries_comm` | `TateFredholm/Fredholm.lean` | proved |
| Lemma 1.15 (= Ser62 Lemme 2) | `charPowerSeries_partition`, `_blockDiag` | `BlockOp.lean` | proved |
| Lemma 1.22 / (1.4.4) (class no. 1) | `HClassNumberOne`, `hClassNumberOne` | `U3/Level.lean` | **contracted `sorry`** (FLT) |
| Def 1.27 + action law | `kappaOp`, `kappaOp_mul` | `U3/KappaAction.lean` (+ `Compose`, `BinomialTheorem`) | proved |
| Def 1.30 (`L(U, A₃)`) | `kappaForms` | `U3/Matrix.lean` | defined |
| Def 1.32 (`[UηU]`) | `heckeU3` | `U3/Matrix.lean` | defined |
| (2.1.1) (`L(U,A₃) ≅ ⊕ᵢ A₃`) | `bijective_evalAtReps` (abstract); `eval_classRep_injective`; `bijective_evalU3`/`kappaFormsModelEquiv` | `QMF/Decomposition.lean`; `U3/Matrix.lean`; `U3/Fredholm.lean` | all proved (2026-08-06) |
| Thm 2.1 (class set) | `classRep_complete` | `U3/ClassSet.lean` | proved (under `hcn`) |
| Lemma 2.2 (`Γᵢ = 1`) | `stabilizerAt_classRep` | `U3/ClassSet.lean` | proved |
| Lemma 2.3 (`Uη₃U` cosets) | `bijOn_etaRep` | `U3/EtaDecomposition.lean` | proved |
| Lemmas 2.4/2.5 + §B.1 | `sigmaTable`/`dTable`/`uTable`/`factorisation`; `adjParams_toMatrix_eq_smul_epsTable` | `U3/Factorisations.lean` | proved (certificates recomputed) |
| Prop 2.6 (gen. fun. of `‖_κ`) | `matrixCoeff_kappaOp`; formula-as-def `weightGenFun`; blocks `sum_weightGenFun_eq_h` | `U3/KappaAction.lean`; `U3Data.lean`; `U3/Factorisations.lean` | proved |
| Displays (2.1.4)–(2.1.9), p. 28 | `eps01M1 … eps21M`, `h01 … h21` | `U3Data.lean` | transcribed + certified (E1 corrected) |
| Lemma 2.7 (integrality/compact) | `norm_coeff_h02/h12_le`; `norm_coeff_h01/h10/h20/h21_le`; `isCompactoid_*` | `U3Data.lean`; `DiamondW.lean` | proved |
| Lemma 2.9 / p. 32 (`W = [UμU]` matrix) | `delta*`, `Wop` (transcribed); identification skeleton `mu3`/`heckeW_apply_classRep`/`actingW_eq_smul_delta` | `DiamondW.lean`; `U3/DiamondHecke.lean` | ticketed (AG-W-ID, WI1–WI7 on jacobs-endgame; certificates computed) |
| Rem 2.8.2 (`W³ = 1`) | `Wop_cube` | `DiamondW.lean` | proved |
| p. 33 (`B`, `3B⁻¹`) | `Bop`, `Binvop`, both inverse relations | `DiamondW.lean` | proved |
| Lemma 2.10 (`B⁻¹AB` diagonal) | `lemma210` | `DiamondW.lean` | proved |
| Lemma 2.11 (six-way identities) | `lemma211_first/first'/second/second'` | `U3Data.lean` | proved |
| Thm 2.12 (slopes `0,1,2,…`) | `norm/val_charCoeff_of_unit_minors`; reading: `unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries` | `SlopeTheorem.lean`; `SlopeReading.lean` | proved |
| Lemma 2.13 | `norm_coeff_NgenFun_le` | `Slopes.lean` | proved |
| Thm 2.14 (`≡ −1/(1−xy)`) | `norm_coeff_NgenFun_sub_negGeom_lt` | `Slopes.lean` | proved |
| Cor 2.15 (unit minors) | `norm_det_NgenFun_minor` | `Slopes.lean` | proved |
| Cor 2.16 (slopes `n − ½`) | vertex data `sq_norm/val_charCoeff_M22op`; reading `unitSlope_newtonPolygon₀OfPowerSeries_M22op`; non-vacuity `slopes_nonvacuous`; **about `U₃`: `charPowerSeriesU3_factorisation`** | `Slopes.lean`; `SlopeReading.lean`; `Instance.lean`; `U3/HeckeSlopes.lean` | all proved (2026-08-06) |
| p. 28 "matrix of `U₃` has the form `A = (ε_{i,j})`" | `heckeU3_apply_classRep` + `charPowerSeries_blockOp_eq_U3MatrixOp`; `det(1−T·U₃)` = `charPowerSeriesU3` (+ `_eq_U3MatrixOp`, proved) | `U3/Matrix.lean`; `U3/Fredholm.lean` | all proved (2026-08-06) |
| (2.1.14) + Lemma 1.15 chain (`det = ∏`) | matrix side `charPowerSeries_U3MatrixOp`; `U₃` side `charPowerSeriesU3_factorisation` (+ `_L₃` witness) | `DiamondW.lean`; `U3/HeckeSlopes.lean` | both proved (2026-08-06) |
| §2.2 (`M₃,₃`, `λ ∈ {1,2}`) | `M33op` + integrality only | `DiamondW.lean` | slope analysis NOT formalised (AG-EXT) |

## 4. Dependency flow

```
                    Mathlib
                       │
        ┌──────────────┼────────────────────┐
 PhD/TateFredholm  PhD/NewtonPolygons   PhD/QMF (AutomorphicFunction,
 (Ser62: charPS,   (polygon spec)       heckeOperator, evalAtReps)
  trace, Riesz)        │                     │
        │              │                     │
  ┌─────┴─────┐        │              U3/Setting ── U3/Hurwitz ── U3/Level [hcn sorry]
PadicAnalytic GenFun   │                     │              │
  │      │     │       │              U3/ClassSet    U3/EtaDecomposition
  │   SlopeTheorem     │                     │              │
  └──┬───┘             │              U3/Compose ── BinomialTheorem
   U3Data              │                     │
     │                 │              U3/KappaAction
   Slopes ─────── SlopeReading ── Instance   │
     │                 │              U3/Factorisations
   BlockOp             │                     │
     │                 │                     │
  DiamondW ────────────┼─────────────► U3/Matrix   (AG-B ↔ AG-W meeting point)
     │                 │                     │
     │            [ENDGAME, open]      U3/Fredholm  ◄── det(1 − T·U₃)
     │                 │                     │
 BaseChange ───────────┴──────────► U3/HeckeSlopes  ◄── factorisation + slopes of U₃
```

Reading order for the headline: `U3/Matrix` (identification) → `U3/Fredholm`
(`det(1−T·U₃)`) → `DiamondW` (factorisation of the matrix) → `U3/HeckeSlopes`
(factorisation of `U₃`) → `SlopeReading` (the `M₂,₂`-factor slopes).

## 5. What is left

**Endgame board** (`.mathlib-quality/jacobs-endgame/`): **all 12 proof tickets + both
notice tickets DONE (2026-08-06, one session)** — E-B (model iso, transport, compactoid,
`det(1−T·U₃)`), E-C (base change, analytic/series/`h`-map layers, transports, the
**milestone factorisation** and its `L₃` witness), E-A (notice rewrites everywhere;
DiamondW keeps the Lemma 2.9 residue).  Every endpoint on the standard three axioms;
full chain green (3519 jobs).  Remaining: the consolidated cleanup wave only (in
progress — per-file /cleanup over the three new files + the DiamondW docstring
punch-list).

**Contracted / deferred (no tickets):**

- `hClassNumberOne` — permanent FLT-interface `sorry` ([Jac Lemma 1.22]); consumers
  hypothesis-parametrised.  Do not fill without user direction.
- **AG-W-ID** — NOW TICKETED (2026-08-06, jacobs-endgame board, WI1–WI7 + skeleton
  `U3/DiamondHecke.lean`): certify the `δ`-blocks as the matrix of the genuine
  `W = [U₁(9)·μ·U₁(9)]`, `μ = diag(4,1)` at 3 (left-handed).  Certificates computed
  (`U3/certificate_search_w.py`: single coset, `σ = (1,2,0)`, `d = ±1`, rational
  diagonal `u`'s; acting matrices reproduce the `δ`-data up to the B15 classWeight
  coboundary).  One API gap: widen the acting monoid `Σ₁(9) → Σ₁(3)` (the three
  `γ₉`-uses in KappaAction already prove the `v(3)` threshold).  End-state: "`M₂,₂` is
  the `ω²`-eigenblock of the diamond operator" becomes a theorem
  (`heckeW_apply_classRep` + `actingW_eq_smul_delta` + `B⁻¹WB = diag(1, ω², ω)`).
- **AG-EXT** — [Jac §2.2]: `M₃,₃` slope analysis, discs `λ ∈ {1,2}`.
- **AG-EIGEN** — eigenvalues of `U₃` from `det(1 − T·U₃)` via `TateFredholm/Riesz.lean`
  (coordinate with the tatefredholm-eigen board; `ℂ₃` is the natural home).
- qmf board tail: BC5 remainder / BCALL-B / BCFINAL-B (cleanups, owned by the parallel
  session), B06/B18 (FLT-deferred).

## 6. Thesis errata (recorded; none break the mathematics)

- **E1** [p. 28] second `ε₁,₂` matrix's `a`-entry misprinted as `−15/14·ν − 5/7`; correct
  value `−5(ν+2)/14 = −5/14·ν − 5/7` (forced by Lemma 2.11's identities, display (2.1.7),
  §B.3's code, and independently by the certificate search).  We use the corrected value.
- **E2** [(2.1.6)] denominator sign `−4y` vs. code/matrices' `+4y`; sidestepped by
  transcribing only the matrices and computing all denominators via `weightGenFun`.
- **E3** [p. 39] "`ν₃ = 2695 + 3¹⁰S`, `S ∈ ℤ₃ˣ`": since `2695² + 2 = 3¹¹·41`, in fact
  `S ≡ 0 mod 3`.  Harmless (only the congruence mod `3¹⁰` is used; our bound is `3¹¹`).
- **E4** [Lemma 2.10 area] "`h₁,₂(7x/10, x, y)`" — three-argument typo for
  `h₁,₂(7x/10, y)`.
- **E5** [p. 32] the `δ`-list names `δ₀,₁` twice; the explicit matrix display below it is
  authoritative (cross-checked by hand from Prop 2.6 at `c = 0, b = 0`).
- **E6** [p. 32] "`W` has minimal polynomial `X² + X + 1`" contradicts the exhibited
  `ker(W − 1) ≠ 0`; correct: `X³ − 1`.  Only `W³ = 1` is used (and proved).
- Understatements: Lemma 2.3 "elementary" (≈ 500 lines); Def 1.27's "easy check" (the
  whole `compAn` + ODE + binomial-theorem development); (1.4.4) cited, not proved.

## 7. Decision records (pointers)

- **Determinant twist** (2026-08-05): certificate blocks differ from the transcribed
  `ε`'s by the coboundary `κ_t(s)s⁻²`, `s = classDet j/classDet i`; kept explicit in
  `matrixCoeff_blockOp` and discharged spectrally (`twist_factor`,
  `charPowerSeries_blockOp_eq_U3MatrixOp`).  Full record: `U3/Matrix.lean` module header.
- **Certificate provenance**: the nine `(σ, d)` triples were *recomputed* by exhaustive
  search (`U3/certificate_search.py`, exact `ℚ(ν)` arithmetic), never transcribed; tables
  and validation record in `U3/Factorisations.lean`'s header.
- **`hcn` contract**: `U3/Level.lean` docstring — the single external `sorry`; axiom
  audits must show `sorryAx` from exactly that source and only in `'`-forms.
- **Endgame design**: E-C finals abstract over isometric `(L, f, ω)`; concrete witness
  `L₃ = CyclotomicField 3 K₃` with mathlib's spectral norm (instances compiled).  Full
  rationale: `.mathlib-quality/jacobs-endgame/{plan,decomposition}.md`.
