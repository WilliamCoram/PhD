# Development Plan: Jacobs Ch. 2 — Slopes of the compact Hecke operator `U₃`

**BOARD PATH: `.mathlib-quality/jacobs/`** — all Jacobs board artifacts live here.
`.mathlib-quality/` (default) = parallel NewtonPolygon board; `.mathlib-quality/qmf/` =
QMF board.  Never read/write/archive those from Jacobs work; every `/beastmode`
invocation for Jacobs must be told this path explicitly.

## Goal
Formalise Chapter 2 of [Jac] (Daniel Jacobs, *Slopes of Compact Hecke Operators*, PhD
thesis, Imperial 2003): the slopes of the `U₃` Hecke operator at level `U₁(9)` are
`1/2, 3/2, 5/2, …` for every weight `κ` in the disc `κ(4) = 4^t`, `v₃(t) > 0`.

**Tranche A (this board)**: the analytic heart — the explicit operator `M₂,₂` (the
`ω²`-eigenblock of `U₃`, defined by its generating function, [Jac (2.1.14)]), through
the abstract slope theorem [Jac Thm 2.12] and the congruence [Jac Thm 2.14], to the
milestone [Jac Cor 2.16]:

```
theorem sq_norm_charCoeff_M22op : ‖charCoeff (M22op …) m‖ ^ 2 = ‖(3:K)‖ ^ (m ^ 2)
```
(`v₃(cₘ) = m²/2` ⇔ slope sequence `1/2, 3/2, 5/2, …`), over an abstract complete
ultrametric field `K` (`‖3‖ < 1`) with parameters `t, ν, ω` — see decomposition.md
"Setting".

**Assumed input / identification debt (user-flagged 2026-08-04, EXPLICIT):** Tranche A
deliberately skips everything the thesis proves before the displays (2.1.4)–(2.1.9) —
Thm 2.1, Lemmas 2.2–2.5, §B.1, and Prop 2.6's derivation.  The `eps*M*` matrices and
`weightGenFun` are *transcriptions/definitions*, so Tranche A's theorems (up to and
including Cor 2.16) are unconditional statements about the explicitly-defined operators,
NOT yet about `U₃ = [Uη₃U]` itself.  Going back to prove these definitions are what we
want = discharging AG-B (and AG-W for the eigenblock identification) — REQUIRED before
any final "slopes of U₃" claim.  Mitigation in place: Lemmas 2.7/2.11 are proved from
the transcribed data and validate its consistency.

**AG-NP tranche OPENED 2026-08-04** (skeleton `PhD/Jacobs/SlopeReading.lean`, tickets
N001–N007): the slope reading via the explicit-witness-against-the-spec method — see
decomposition.md "AG-NP tranche" incl. the approach comparison (explicit witness vs
slope-induction).  Endpoints: `IsNewtonPolygonOf (v₃∘cₘ) (ofSlopes s)` and
`(newtonPolygon₀OfPowerSeries v₃ (charPowerSeries ·)).unitSlope j = s j` for both slope
sequences; case A (Thm 2.12, slopes 0,1,2,…) first as PoC per user.

**AG-W tranche OPENED 2026-08-04** (skeleton `PhD/Jacobs/{BlockOp,DiamondW}.lean`,
tickets W001–W011): the diamond operator, `W³ = 1`, Lemma 2.10 block-diagonalisation,
and the milestone `det(1−T·U₃) = ∏ det(1−T·M_{t,t})` via Serre's partition lemma
(stated at TateFredholm generality in BlockOp.lean — upstreaming candidates).  Two new
thesis errata (findings 6–7).  M₃,₃'s OPERATOR defined here; its slope analysis stays
AG-EXT.

**Deferred tranches** (recorded as AG-NP / AG-W / AG-EXT / AG-B in decomposition.md,
NO tickets yet): the Newton-polygon-language wrapper (coordinate with the parallel
NewtonPolygon board), the `W`-operator eigenspace splitting, the §2.2 extensions
(`M₃,₃`, `λ ∈ {1,2}` discs), and the adelic identification (QMF instantiation at
`D = (−1,−1)_ℚ`, class number one via the Hurwitz-Euclidean route, the coset
computations, `U₃ = [Uη₃U]`).  **AG-B is blocked on QMF-board infrastructure**: the
tensor-restricted-product / `mulSingle` port that QMF T017 is waiting for (T015/T016
closure).  NOTE TO COME BACK: when the QMF board lands T016/T017, open the AG-B
tranche here with `/develop --continue`.

## References
- [Jac] the thesis PDF (user-supplied).  Ch. 2 pp. 22–40; §1.1 pp. 6–8; §1.2 pp. 8–12.
- [Kob84] Koblitz GTM 58, Ch. IV — p-adic exp/log discs (thesis's own reference; used
  for the analytic API gap per the source-gap fallback chain).
- [Ser62] Serre IHÉS 12 — already formalised as `PhD/TateFredholm/`.
- [Vig80] Vignéras LNM 800 — reserved for AG-B.2 (class number one).

## Infrastructure inventory
| Concept | Status | Action |
|---|---|---|
| Banach space `c(ℕ,K)`, operators, `matrixCoeff`, `rowNorm`, `IsCompactoid` | `PhD/TateFredholm/{ModelSpace,Matrix}.lean`, sorry-free | USE |
| `charCoeff`, `charPowerSeries`, trace property `charPowerSeries_comm` | `PhD/TateFredholm/Fredholm.lean`, sorry-free | USE (the [Jac §1.2] layer, entirely done) |
| `PseudoUniformizer.val` (`v₃`, `WithTop ℝ`) | `PhD/TateFredholm/Tate.lean` | USE for the milestone's val form |
| p-adic `exp`/`log`/binomial series + discs | NOT in mathlib (checked this session) | NEW: `PhD/Jacobs/PadicAnalytic.lean` (API gap R1) |
| `MvPowerSeries` coeff/C/X/field-inverse | mathlib (`coeff (n)`, `C` implicit-typed at this rev) | USE |
| Legendre `v₃(n!)` | mathlib `padicValNat` + factorial lemmas | USE |
| Newton polygon slopes | `ForMathlib/NumberTheory/NewtonPolygon/` — parallel board, API in flux (B2 log) | DEFER (AG-NP); milestone in `val`/norm form |
| Quaternionic `L(U,A)`, Hecke `[UηU]`, class-set decomposition | `PhD/QMF/`, sorry-free | DEFER to AG-B (needs QMF T017's port blocker resolved) |

## File structure (skeleton built + `lake build PhD.Jacobs.Slopes` green, 2026-08-03)
```
PhD/Jacobs/PadicAnalytic.lean  -- exp/log/unitPow/binomial over ultrametric K (R1)
PhD/Jacobs/GenFun.lean         -- matrices ↔ MvPowerSeries ↔ operators; D(α); Cor 1.10 (R2)
PhD/Jacobs/SlopeTheorem.lean   -- Thm 2.12 abstract slope theorem (R3)
PhD/Jacobs/U3Data.lean         -- the 9 ε-matrices, six h's, Lemma 2.7, Lemma 2.11, M₂,₂ (R4)
PhD/Jacobs/Slopes.lean         -- Lemma 2.13, Thm 2.14, Cor 2.15/2.16 milestone (R5)
```

## Dependency graph (tickets)
```
J001→J002→J003→[CJ1]→J004→[CJ2]        (PadicAnalytic)
J005→J006→J008 ; J005→J007→[CJ3 after J007]→…→[CJ4]   (GenFun; J009,J010 parallel anytime)
J009,J010→J011→[CJ5]                    (SlopeTheorem; J009∥J010∥J005…)
J004,J005→J012→J013 ; J012,J003→J014→[CJ6]→J015 (needs J006,J008,J013)→[CJ7] (U3Data)
J016∥ ; J004,J012,J016→J018→J017,J019→[CJ8] ; J015,J008,J010→J020 ;
J011,J019,J020→[CLEANUP-ALL]→J021 (MILESTONE)→[CLEANUP-FINAL]   (Slopes)
```

## Generality decisions
- Abstract `(K, t, ν, ω)` with hypothesis-parameters instead of `ℂ₃` (see
  decomposition.md "Setting"); `‖2ω+1‖² = ‖3‖` derived, not assumed.
- Norms not valuations in working statements; half-integers as squared norms; `𝔪₃` as
  strict inequalities.  `val`-forms only at the two slope-statement endpoints.
- `isCompactoid_of_row_decay` generalises [Jac Cor 1.10] from `q = 3` to any `‖q‖ < 1`.
- Thm 2.12's "compact" hypothesis dropped (implied by the divisibility hypothesis).
- PadicAnalytic is deliberately mathlib-shaped (candidate for eventual upstreaming;
  keep it free of Jacobs-specific constants beyond the prime 3 — a `p`-generic pass is
  a possible later /generalise target, NOT in scope now).

## Conventions / hazards for workers
- **Row/column convention**: thesis `(n_{ji})` rows `j` = output index = TateFredholm
  `matrixCoeff u j i` first argument = our `x`-degree in `idx j i`.  Re-verify at J006
  against `TateFredholm/Matrix.lean:34` before building on it.
- `MvPowerSeries (Fin 2) K` is a function type; `coeff p F` is defeq `F p` — the
  `diagRescale`/`kappaSeries₂` defs exploit this; keep their `@[simp]` coeff lemmas the
  only interface downstream.
- Section-variable `include` is load-bearing in all five files (statements' hypotheses).
- Data entry is sacred: the eight `eps*M*` matrices carry two thesis errata already
  resolved (decomposition.md findings 1–3).  If J014 (Lemma 2.11) fails, suspect the
  plan's data before inventing mathematics — and re-open decomposition.md.
