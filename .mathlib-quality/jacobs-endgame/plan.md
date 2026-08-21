# Development Plan — Jacobs endgame: `U₃`-refactor of the downstream slope files

**BOARD PATH: `.mathlib-quality/jacobs-endgame/`** (NOT the default board = NewtonPolygons,
NOT `jacobs/` = the completed Tranche-A/AG-NP/AG-W board, NOT `qmf/` = the completed AG-B
board, NOT `tatefredholm-eigen/`).  Every `/beastmode` invocation must be told this path.

## Goal

Discharge the **identification debt** recorded in `PhD/Jacobs/U3Data.lean` §"Assumed
input": the Tranche-A / AG-W slope results are unconditional statements about
*explicitly-defined operators* (transcribed `ε`-matrices, `weightGenFun` taken as a
definition); AG-B (qmf board, complete 2026-08-05) proved Thm 2.1, Lemma 2.2, Lemma 2.3,
Lemmas 2.4/2.5 (the nine certificates), Prop 2.6 (the `κ`-action's generating function =
`matrixCoeff_kappaOp`), and the meeting-point bridges in `PhD/Jacobs/U3/Matrix.lean`
(`heckeU3_apply_classRep`, `eval_classRep_injective`,
`charPowerSeries_blockOp_eq_U3MatrixOp`).  This board **refactors the downstream files to
consume those proofs**: the headline slope results become statements about the genuine
Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on `L(U₁(9), A₃)`, and the "assumed" notices are
replaced by pointers to the proofs.

Three tranches:

* **E-A (notices).**  Rewrite the "Assumed input" / "unconditional about the defined
  operators" module-header notices of `U3Data.lean`, `Slopes.lean`, `SlopeTheorem.lean`,
  `DiamondW.lean`, `SlopeReading.lean` to record the identification as *proved* (with
  decl-level pointers).  Documentation only — zero statement changes.
* **E-B (the `K₃`-level endgame).**  `det(1 − T·U₃)` becomes a genuine object:
  the model isomorphism `kappaForms ≅ c(Fin 3 × ℕ, K₃)` (evaluation at the class
  representatives; surjectivity is the one new proof, via QMF's abstract
  `bijective_evalAtReps` + Lemma 2.2's trivial stabilizers), the transport
  `heckeU₃ ↦ TateFredholm.blockOp (U3.blockOp t ht)`, compactoidness, and the headline
  `charPowerSeriesU3 t ht = charPowerSeries (U3MatrixOp …)` over `K₃`.
* **E-C (the `ω`-extension endgame).**  `K₃ = ℚ₃` has no primitive cube root of unity
  (the U3Data header records this: `hω` forces `K ⊇ ℚ₃(ζ₃)`, ramified quadratic), so the
  eigenblock factorisation and the `M₂,₂` slope reading need a coefficient extension.
  Primary statements are **abstract over `(L, f, ω)`** — `L` a complete ultrametric
  `NontriviallyNormedField`, `f : K₃ →+* L` isometric, `ω ∈ L` with `ω² + ω + 1 = 0`:
  - base-change of the Fredholm determinant (`charPowerSeries_map`, TateFredholm
    generality — matrix-level `matrixCoeff v = f ∘ matrixCoeff u` implies
    `charPowerSeries v = PowerSeries.map f (charPowerSeries u)`),
  - map-compatibility of the analytic layer (`padicLog/padicExp/unitPow`, the six `h`
    series) so `U3MatrixOp` over `L` at `(f t, f ν₃)` has matrix `f ∘` the `K₃` one,
  - final theorems: `PowerSeries.map f (charPowerSeriesU3 t ht)
    = charPS(M₁,₁) · charPS(M₂,₂) · charPS(M₃,₃)` over `L` (thesis (2.1.14) + Lemma 1.15
    as a `U₃` statement) and the `M₂,₂`-factor Newton-polygon slopes `n − 1/2`
    (SlopeReading case-B instantiated at `L`) — thesis Cor 2.16 **about `U₃`**.
  - a concrete witness `(L₃, f, ω₃)` [feasibility section below].

Deliberately **out of scope** (mirroring the thesis): a Newton-polygon-of-products merge
theorem (the thesis never proves one — it stops at "the `n`-th slope of `M₂,₂` is
`n − 1/2`"); `hClassNumberOne` (permanent contracted `sorry`, FLT interface — every
consumer takes `hcn` as an explicit hypothesis, matching `eval_classRep_injective`);
AG-EXT (`λ ∈ {1,2}`, `M₃,₃` slopes).

## References

- [Jac] Jacobs, *Slopes of Compact Hecke Operators* (thesis PDF not in repo; all verbatim
  quotes reused from the recorded quote inventory in `.mathlib-quality/jacobs/decomposition.md`,
  `.mathlib-quality/qmf/decomposition.md`, and `PhD/Jacobs/PROGRESS.md` — these boards
  quoted the source precisely for this reuse).
- [Buz07] §9 p. 69 (quoted, qmf board R5): `f ↦ (f(τ_λ))` is an isomorphism
  `L(U,A) → ⊕ A^{Γ_λ}` — the E-B iso's source.
- Project sources (this is a refactor board — the "source proofs" are largely our own
  proved declarations): `PhD/Jacobs/U3/Matrix.lean` (meeting point), `PhD/QMF/`
  (`bijective_evalAtReps`, `heckeOperator_apply_rep`), `PhD/Jacobs/BlockOp.lean`,
  `PhD/Jacobs/DiamondW.lean` (AG-W endpoints), `PhD/Jacobs/SlopeReading.lean` (case B),
  `PhD/TateFredholm/` (charPowerSeries, minors, summable_minor).

## Mathlib inventory

| Concept | Status | Action |
|---|---|---|
| `PowerSeries.map` / `MvPowerSeries.map` | mathlib | USE for base-change statements |
| map of inverse power series | verify at decompose | USE or small private lemma |
| Spectral norm on finite extensions | VERIFY (feasibility gate below) | decides concrete-`L₃` layer |
| `CyclotomicField 3 K₃` | mathlib | candidate concrete `L₃` |
| finite-dim over complete ⇒ complete | mathlib (`FiniteDimensional.complete`) | verify name |
| Fredholm base change (`charPowerSeries_map`) | NOT in mathlib/TateFredholm | DEFINE (PR-shaped, TateFredholm generality) |

## File structure (new files; existing files touched only by E-A notices)

- `PhD/Jacobs/BaseChange.lean` — `TateFredholm.charPowerSeries_map` + the Jacobs
  analytic map-compat layer (`map_padicExp` … `map_h`-series).
- `PhD/Jacobs/U3/Fredholm.lean` — E-B: model iso, transport, compactoid,
  `charPowerSeriesU3`, `K₃` headline.
- `PhD/Jacobs/U3/HeckeSlopes.lean` — E-C finals: abstract `(L, f, ω)` factorisation +
  `M₂,₂`-factor slope corollaries (+ concrete `L₃` instantiation if feasible).

## Dependency graph

```
E-B: iso (surjectivity) ─→ transport ─→ charPowerSeriesU3 + K₃ headline ─┐
     compactoid ────────────────────────────────────────────────────────┤
E-C: charPowerSeries_map ─┐                                             ├─→ E-C finals
     analytic map-compat ─┴─→ map of U3MatrixOp charPS ─────────────────┘   (factorisation,
                                                                             M₂,₂ slopes)
E-A notices: after E-B milestone (they cite its decl names)
```

## Generality decisions

- E-C primary statements abstract over `(L, f, ω)`: maximal generality, and keeps the
  endgame independent of mathlib's norm-extension API; the concrete witness is a
  corollary layer.  `f : K₃ →+* L` with `∀ x, ‖f x‖ = ‖x‖` (isometric ring hom — gives
  continuity for tsum transport and preserves every norm hypothesis).
- `charPowerSeries_map` at TateFredholm generality (matrix-level hypothesis, no
  operator-level base-change construction — consumers instantiate the target operator
  directly).
- `hcn : HClassNumberOne` as explicit hypothesis everywhere it is needed (iso layer);
  the transport/charPowerSeriesU3/factorisation layer is `hcn`-free (it is about the
  certificate block operator, which is unconditional).

## Feasibility gate (resolved before ticketing)

Concrete-`L₃` layer: pending the mathlib search verdict on spectral-norm/norm-extension
API (recorded in decomposition.md when it lands).  If mathlib supports it: one ticket
constructs `L₃` (cyclotomic route, no irreducibility proof needed) and instantiates the
abstract finals.  If not: the concrete witness is recorded as an explicit API gap with
its own future tranche; the abstract finals stand as the board's E-C milestone.
