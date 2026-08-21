# Development Plan — slopes-hecke (`.mathlib-quality/slopes-hecke/`)

**BOARD PATH: `.mathlib-quality/slopes-hecke/`** (not the default board).  Planned 2026-08-20 by
`/develop` from the four items the user selected after forms-riesz.  Status: **AWAITING VERDICT**.

## Goal

**(A) Slopes of `det(1 − T·[UηU])` at a general analytic weight.**  Row decay of the matrix —
the same estimate that makes `[UηU]` compact — bounds the coefficients of the Fredholm
determinant, hence bounds its Newton polygon from below.  New: `TateFredholm/Slopes.lean` (the
σ-general, weight-free half of the fork's `1_SlopeTheorem`), `QMF/Weight/Slopes.lean` (the
same at a general weight), and the move of `NewtonPolygon₀.ofSlopes` out of the fork.

**(B) Hecke algebra.**  Following [Buz07 §5 p. 33] *exactly*: commutativity is **data**, not a
theorem ("`T` is a commutative `R`-algebra equipped with an `R`-algebra map `T → End_R(M)`,
such that the endomorphism induced by `φ ∈ T` is compact").  We prove what the machine
consumes: a commuting operator preserves the Riesz finite-slope subspace, and a commuting
family on a finite-dimensional space over an algebraically closed field has a common
generalised eigenvector — i.e. a *system of eigenvalues*.  Plus the abstract commutation
criterion for double-coset operators (whose discharge for `T_v`, `T_w` is Satake-theoretic and
is **not** ticketed — the source does not prove it either).

**(C) The valuation ↔ norm level dictionary.**  Corrected scope after the user's observation:
mathlib's `Valued.toNormedField.norm_le_iff` (norm = rank-one image of the valuation, strictly
monotone) supplies all three hypotheses of `Sigma0'.levelBounds`, verified as a 10-line lemma
during planning.  The AddVal layer is *not* needed for the order dictionary; what remains is
the `Σ₁`-type level in general form (`SigmaOne K ρ`, generalising the fork's `sigma1Norm`) and
its valuation description, after which the fork's hand-rolled `norm_le_of_valued_le` /
`norm_eq_one_of_valued_eq_one` are deleted.

**(D) Compact open levels (forms-riesz T009, undeferred).**  `Units.embedProduct` is a closed
embedding, so units of a compact set form a compact set; the integral order of `D` in
`D ⊗ 𝔸_F^∞` is the image of `(integralAdeles)^n` under a continuous map, hence compact.  Then
the fork's `U0` / `U₁(9)` are compact open and the Hecke finiteness hypothesis is automatic.

## References
- [Buz07] Buzzard, *Eigenvarieties* (LMS 320): §5 p. 33 (the Hecke-algebra datum), §9 pp. 68–69
  (compact open level; `UηU = ∐ U xᵢ`), §13 pp. 79–80 (the determinant of `U_π` in families).
- [Jac03] Jacobs, thesis: Thm 2.12 (pp. 34–35), Lemma 2.7, §2.1 p. 29 (the `Σ₁` congruences).
- [Ser62] Serre, *Endomorphismes complètement continus*, §5 (Hadamard/Fredholm coefficient
  bounds) — formalised in `TateFredholm/Fredholm.lean` (`minor`, `charCoeff`).

## Mathlib / project inventory
| Concept | Status | Action |
|---|---|---|
| `‖x‖ ≤ ‖y‖ ↔ v x ≤ v y` at valued fields | **mathlib** `Valued.toNormedField.norm_le_iff` (+ `norm_le_one_iff`, `one_le_norm_iff`, `norm_lt_one_iff`) | USE — this is (C)'s dictionary |
| ultrametric Hadamard bound | project `TateFredholm.norm_det_le_of_row_bounds` (private, Fredholm.lean:37), fork `norm_det_le_of_row_bound` (1_SlopeTheorem.lean:67, at `‖3‖`) | GENERALISE to σ + row weights |
| `‖minor u S‖ ≤ …` | project `norm_minor_le_prod` (rowNorm form), fork `norm_minor_le_pow_sum` (private, at `‖3‖`) | GENERALISE |
| row decay at a general weight | project `norm_matrixCoeff_kappaSlash_le` (SlashAction.lean:386) | USE |
| `ofSlopes`, `IsNewtonPolygonOf.isGreatest` | project `4_SlopeReading.lean:73` (in the fork), `NewtonPolygons/Spec.lean:71` | MOVE `ofSlopes` to `NewtonPolygons/`; USE `isGreatest` for "lies above" |
| commuting-family eigenvectors | mathlib `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo` (Eigenspace/Pi.lean:148) | USE |
| `Units.isClosedEmbedding_embedProduct` | **mathlib** (Topology/Algebra/Group/Basic.lean:1422) | USE for (D) |
| `isCompact_integralAdeles` | project FLTstuff (`Mathlib/NumberTheory/NumberField/FiniteAdeleRing.lean:55`) | USE for (D) |
| `RigidificationAt` from "D splits at v" | not in mathlib, not in project | **OUT OF SCOPE** (per-example data; noted in §5 of the README) |

## File structure (skeleton in place, `lake build` green, 18 sorries)
- `PhD/TateFredholm/Slopes.lean` (NEW, 5 sorries): `norm_det_le_pow_of_row_bound`,
  `norm_minor_le_pow_sum`, `norm_charCoeff_le_pow` (weighted), `choose_two_le_sum`,
  `sum_div_le_sum_block`, + the two corollaries.
- `PhD/NewtonPolygons/OfSlopes.lean` (NEW, refactor — no skeleton): the `NewtonPolygon₀.ofSlopes`
  section moved out of `PhD/JacobsSlash/4_SlopeReading.lean`.
- `PhD/QMF/Weight/Slopes.lean` (NEW, 3 sorries): `norm_matrixCoeff_heckeBlock_le`,
  `norm_matrixCoeff_heckeBlockOp_le`, `norm_charCoeff_heckeCharPowerSeries_le`, and (ticket A5)
  the Newton-polygon statement.
- `PhD/QMF/Weight/HeckeAlgebra.lean` (NEW, 3 sorries): `heckeOperatorSlash_comm_of_reps`,
  `mapsTo_ker_of_commute`, `exists_common_eigenvector`, + (ticket B4) the eigen-system on the
  Riesz subspace.
- `PhD/QMF/Weight/AdicLevel.lean` (NEW, 5 sorries): `Sigma0'.levelBounds_valued`, `SigmaOne`,
  `levelBounds_sigmaOne`, `mem_sigmaOne_iff_valued`.
- `PhD/QMF/Level.lean` (NEW, 2 sorries): `Units.isCompact_of_isCompact`, `integralTensor`,
  `isCompact_integralTensor`; + (ticket D3) `U0`/`U₁(9)` compact in the fork.
- Fork edits: `4_KappaColumn.lean` (delete the two dictionary lemmas), `5_KappaWeight.lean`
  (`sigma1Norm := SigmaOne K₃ ‖3‖`), `1_SlopeTheorem.lean`/`4_SlopeReading.lean` (instances of
  the general slope layer), `U3/2_Level.lean` (compactness).

## Dependency graph
```
A1 (TateFredholm/Slopes) ─► A2 (fork 1_SlopeTheorem as instances) ─► CLEANUP-1
A0 (move ofSlopes)  ─────────────────────────────────────────────► A5
A1 ─► A3 (row decay of heckeBlockOp) ─► A4 (charCoeff bound at general weight) ─► A5 (Newton polygon lies above, MILESTONE) ─► CLEANUP-2
B1 (comm criterion) ; B2 (mapsTo_ker) ; B3 (common eigenvector) ─► B4 (eigen-system on the Riesz subspace, MILESTONE) ─► CLEANUP-3
C1 (levelBounds_valued) ─► C2 (SigmaOne + bounds) ─► C3 (valuation form) ─► C4 (fork: sigma1Norm := SigmaOne, delete dictionary lemmas) ─► CLEANUP-4
D1 (units of compact) ─► D2 (integral order compact) ─► D3 (fork U0/U₁(9) compact + Hecke finiteness) ─► CLEANUP-5
all ─► CLEANUP-FINAL
```

## Generality decisions
- (A) The slope bound takes a **row weight** `w : I → ℕ` and an arbitrary lower bound `f n` for
  the weight sum over `n`-element sets — because the block model is indexed by `ι × ℕ`, not `ℕ`,
  so the fork's `n choose 2` is the `I = ℕ, w = id` instance and the block case is
  `w = Prod.snd`, `f n = ∑_{k<n} ⌊k/|ι|⌋`.
- (A) Inequality, not equality: equality needs Jacobs's unit-minor hypothesis (his Cor 2.15),
  which is weight-specific; the general theorem is the lower bound on slopes.
- (B) Commutativity as data (Buzzard's own framing).  The criterion `…_comm_of_reps` is stated
  with the pairing hypothesis rather than "disjoint support", because coset representatives
  `η·u` at different places do **not** commute elementwise — a naive "disjoint support ⇒
  commuting" leaf would be false.
- (C) `Sigma0'.levelBounds_valued` takes `y` with `Valued.v y = γ` and yields `ρ = ‖y‖` — no
  discreteness, no uniformizer, no `AddVal` needed.  `SigmaOne K ρ` uses `ρ²`/`ρ` (Jacobs's
  `p² | c`, `p | d−1`); the fork's `sigma1Norm` becomes its `ρ = ‖3‖` instance.
- (D) The compactness route avoids restricted products: image of a compact set under a
  continuous map.  `Module.Finite F D` (not `DivisionRing`) suffices for the order; the unit
  lemma is stated for any `T1` topological monoid.
