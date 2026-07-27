# Development Plan: Weierstrass division & preparation (Option B, Tranche 1)

## Goal
Port the Weierstrass division and preparation theory from the legacy
`PhD/WeierstrassPrep/` tree into `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/`, in the
**Option-B architecture** with a **general-radius public API**:

- `PowerSeries.IsDistinguished v c f s` — the weighted predicate (the legacy
  `distinguishedGen`) is THE predicate; no unweighted variant exists.
- Division bounds and uniqueness: stated and proven at arbitrary radius `c`
  (`Fact (0 < c)`), direct weighted proofs, no auxiliary hypotheses.
- Division existence and preparation: stated at radius `c` with
  `hα : ∃ u : Rˣ, ‖(u : R)‖ = c`, proven by rescaling (`Restricted.rescaleEquiv`) into a
  radius-`1` engine (residue-monic reduction, ε-approximate division, dense + closed
  subgroup — the reduction of `T°` is a polynomial ring only at radius 1).
- No `c = 1`-labeled public theorems: `c = 1` is the instance `u = 1`.

Milestones: `weierstrassDivision_uniqueness` and `weierstrassPreparation_unique` at general
radius, sorry-free, standard axioms.

## References (all machine-checked Lean, this repository)
| Source | Role |
|---|---|
| `PhD/WeierstrassPrep/WeierstrassDivision.lean` (890 l) | division engine + bounds (radius 1) |
| `PhD/WeierstrassPrep/WPrep.lean` (444 l) | preparation engine (radius 1) |
| `PhD/WeierstrassPrep/WPrep_gen.lean` §0 (84–131), §2 (162–365) | weighted predicate; rescale isometry; transport pattern |
| `PhD/ForMathlib/.../Restricted/{Residue,Units,GaussNorm,...}.lean` | the new-tree machinery the port re-points to |

## Mathlib inventory (names verified)
| Concept | Status | Action |
|---|---|---|
| Weierstrass division/preparation (restricted series) | not in mathlib | THIS DEVELOPMENT |
| ε-dense subgroup ⇒ dense | `AddSubgroup.dense_of_infDist_le` (ForMathlib HausdorffDistance.lean, BGR 1.1.4/2) | USE (replaces legacy EpsilonDense) |
| polynomial lifting along quotients | `Polynomial.lifts_and_degree_eq`, `lifts_iff_set_range`, `Polynomial.map_surjective` | USE (replaces legacy Polylift) |
| `X ^ s - r` monic (deg r < s) | `Polynomial.monic_X_pow_sub` | USE (replaces legacy test1–4) |
| rescaling of power series | `PowerSeries.rescale`, `coeff_rescale`, `rescale_rescale`, `rescale_one` | USE |
| monic Euclidean division | `Polynomial.modByMonic_add_div`, `degree_modByMonic_lt`, `div_modByMonic_unique` | USE |
| residue maps, ball ideals, unit criteria | new ForMathlib tree (Residue/Units) | USE |

## File structure (skeleton written, `lake build` green, 42 sorries + 2 def-data sorries)
- `Restricted/Distinguished.lean` — `IsDistinguished` + basic lemmas (general c)
- `Restricted/Rescale.lean` — `rescaleEquiv : Restricted R c ≃+* Restricted R c'`
  (generalised target radius), isometry, polynomial transport, distinguished-iff
- `Restricted/WeierstrassDivision.lean` — bounds/uniqueness (general c) + engine (c = 1) +
  existence (general c, `hα`)
- `Restricted/WeierstrassPrep.lean` — preparation (general c, `hα`) + engine (c = 1)

## Dependency graph
```
Distinguished ──→ Rescale ──→ WeierstrassDivision ──→ WeierstrassPrep
                                (bounds ⟂ engine; existence needs both + Rescale)
                                (engine needs Residue + Units + HausdorffDistance)
```

## Generality decisions
- Weighted predicate at `Semiring R`, `v : R → ℝ` (source §0 context; maximal).
- `rescaleEquiv` at general source AND target radii (`‖u‖ * c' = c`) — the source's
  `c' = 1` computation is the general one with `1ᵏ` erased; costs nothing.
- `norm_units_inv` weakened from `‖u‖ = c > 0` to `‖u‖ ≠ 0` (all the proof uses).
- `[Nontrivial R]` never assumed where `[NormOneClass R]` is present (implies it).
- The `hunit` scaling hypothesis kept verbatim (`∀ f ≠ 0, ∃ a, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a`) —
  automatic over normed fields; packaging it is deferred (legacy source comment, cleanup-time
  decision).
- `hα : ∃ u, ‖u‖ = c` confined to existence/preparation; identified future work (C-probe)
  may remove it by a direct weighted ε-division engine.

## Deferred to later tranches (`/develop --continue`)
- USER ROADMAP (2026-07-25) for removing the value-group constraint hidden in `hunit`:
  (1) rung 2 — division/preparation for every `c` in the DIVISIBLE CLOSURE of `‖Rˣ‖`
  (WPrep_gen §4–§5: finite extensions, spectral norm, descent; DivValueGroup API);
  (2) density of the divisible closure in `ℝ_{>0}` (nontrivial norm, from NeBot) + limits
  in `c` to reach all `c > 0`.  Backbone already shipped: hypothesis-free bounds and
  q-uniqueness at every radius (uniform estimates + coherence), general-radius tail bound
  (board note).  Pressure point: distinguishedness under radius perturbation when a `t < s`
  term ties the Gauss sup (degree drops; over a field the limit divisions still converge to
  a valid degree-`s` division).
- Rung 2 details (radii with `cⁿ = ‖x‖`; finite extensions, spectral norm, descent) —
  WPrep_gen §4–§5.
- Multivariate preparation (WPPrep_MV.lean).
- Univariate `Restricted.X`-API and packaging of `hunit` (flagged in legacy comments).

---

# Tranche 2: Weierstrass theory at every radius (approved 2026-07-25)

## Goal
Over a complete nontrivially normed ultrametric field `K`, Weierstrass division and
preparation at **every** radius `c > 0` with no scaling hypotheses:
`weierstrassDivision_{exists,uniqueness,polynomial}_of_field` and
`weierstrassPreparation_{exists,unique,polynomial}_of_field` in `Restricted/DivisibleRadius.lean`.

## Architecture (user-approved design decisions)
1. **Prep-as-corollary**: `weierstrassPreparation_exists_of_forall_exists` derives
   preparation from division existence + the hypothesis-free `weierstrassDivision_q_unique`
   (divide `X^s` by `g`, then `g` by the resulting `ω`, then compare `g = g·(q·P) + S` with
   `g = g·1 + 0`). Preparation is instantiated at each division generality (hunit /
   divisible / every-radius) — never re-proven. The shipped radius-1 residue prep engine is
   deleted (T025); the division-side residue machinery stays.
2. **Rung 2 (divisible closure)**: port of WPrep_gen §4–§5 division-only.
   `Restricted/BaseChange.lean` (isometric `mapAlgebra`, distinguishedness transport,
   descent-by-uniqueness via a bounded linear retraction) + division at
   `MemDivisibleValueGroup` radii via the spectral-norm extension `K⟮α⟯`, `α^n` a root of
   the realising element. The legacy prep-descent (~310 lines incl.
   `isUnit_of_isUnit_mapAlgebra`) is NOT ported — dead under prep-as-corollary.
3. **Dichotomy, not limits**: off the divisible closure, a Gauss-term tie against the unit
   coefficient `aₛ` would exhibit `c^(s−t) = ‖aₜ·aₛ⁻¹‖` — impossible; so the `s`-term
   strictly dominates and the direct one-step contraction division (BGR §5.2.1/2 shape,
   `T(f) = u⁻¹·(s-shift)`, error factor `θ < 1` from T033) runs at the radius itself over
   general `R`, through the same dense (`AddSubgroup.dense_of_infDist_le`, `ε := θ`) +
   closed (generalized `isClosed_divisionSet`) architecture. The density+limits route was
   rejected: coherent approximating quotients at `cₖ ↑ c` are a single power series whose
   boundedness at `c` does not imply restrictedness at `c` (shape `Σ c⁻ᵗXᵗ`).

## Mathlib inventory (verified by the compiled legacy at this pin)
`spectralNorm.nontriviallyNormedField`, `spectralNorm_extends`,
`isNonarchimedean_spectralNorm`, `IsAlgClosed.exists_pow_nat_eq`,
`IntermediateField.adjoin.finiteDimensional`, `FiniteDimensional.complete`,
`NormedField.nhdsNE_neBot`, `LinearMap.exists_leftInverse_of_injective`,
`SemilinearMapClass.bound_of_continuous`, `LinearMap.continuous_of_finiteDimensional`,
`PowerSeries.trunc`/`coeff_trunc`/`degree_trunc_lt`, `pow_sub₀`.

## File structure
- `Restricted/BaseChange.lean` (new) — mapAlgebra + descent
- `Restricted/DivisibleRadius.lean` (new) — `MemDivisibleValueGroup`, divisible-radius
  theorems, no-tie lemma, every-radius milestones
- `Restricted/WeierstrassDivision.lean` — division-set trio generalized to `c` (T024);
  strictly-dominated engine (T033–T035)
- `Restricted/WeierstrassPrep.lean` — the prep-as-corollary trick (T025); engine deleted

## Generality decisions
- Base-change layer at `NormedCommRing` (no fields); distinguishedness transport and
  descent at `NontriviallyNormedField` (unit-reflection and finite-dim continuity are
  genuinely field-level, per the §4 generality note).
- The strictly-dominated engine (T033–T035) and the no-tie lemma (T036) at general `R` —
  deliberately not field-only; the dichotomy finals are field-level because rung 2 is.
- `MemDivisibleValueGroup` self-contained over `[Norm K]`; the DivValueGroup divisible-hull
  bridge is deferred to the Newton-polygon tranche (user decision).

## Deferred (tranche 3+)
- Multivariate: Mv division by induction on variables (univariate over Tate-algebra base at
  radius 1, hunit via constant units); Mv prep = the same corollary trick.
- Newton-polygon bridge (`DivValueGroup.lean` hull API ↔ `MemDivisibleValueGroup`).
- `_of_field` naming consolidation (CLEANUP-13) and `hunit` packaging.

## Tranche 3b (2026-07-25): every-polyradius Mv Weierstrass — Gauss-extension route approved by user ("ultimate goal"). Régime-B endpoints deleted pre-implementation; public API = unconditional six. New: LaurentPolynomial/GaussNorm + GaussExtension layers; 1-var descend refactored to retraction form (PROVEN). See decomposition.md tranche-3b.
