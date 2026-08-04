# Development Plan: Zeros of the characteristic power series are eigenvalues (Serre's Riesz theory)

**Board**: `.mathlib-quality/tatefredholm-eigen/` — this board is separate from
`.mathlib-quality/` (NewtonPolygon agent), `.mathlib-quality/qmf/` (QMF) and
`.mathlib-quality/jacobs/` (Jacobs). Every beastmode invocation for this project must name
this board explicitly. **New Lean file only** (`PhD/TateFredholm/Riesz.lean`); no edits to
existing TateFredholm files, which the NewtonPolygon agent may be touching concurrently.

## Goal

Over a complete nonarchimedean field `K` (repo setting: `[NontriviallyNormedField K]
[IsUltrametricDist K] [CompleteSpace K]`, which gives `IsTate K` by instance), for a
compactoid operator `u : c(I, K) →L[K] c(I, K)` with characteristic power series
`H := charPowerSeries u` and a point `a : K` at which the entire series `H` evaluates to
zero, produce an eigenvector:

```lean
theorem exists_eigenvector_of_evalT_charPowerSeries_eq_zero
    (hu : IsCompactoid u) {a : K} (ha : evalT a (charPowerSeries u) = 0) :
    a ≠ 0 ∧ ∃ x : c(I, K), x ≠ 0 ∧ u x = a⁻¹ • x
```

together with the converse (Serre's Proposition 11: `1 − a•u` is invertible iff
`H(a) ≠ 0`), so that **the zeros of `det(1 − Tu)` are exactly the reciprocals of the
nonzero eigenvalues of `u`**. This is the last link in the slopes story: the Newton
polygon of `charPowerSeries u` (NewtonPolygon board + Koblitz GTM 58 Ch. IV) locates the
valuations of the *zeros* of `H`; this development converts each zero into an
*eigenvalue* of `u` of the reciprocal valuation.

## References

| Tag | Reference | Role |
| --- | --- | --- |
| `[Serre]` | J-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*, Publ. Math. IHÉS **12** (1962), 69–85. numdam PMIHES_1962__12__69_0 | **Primary.** §5 Prop 7 + Cor 1 (p. 76: multiplicativity `det((1−tu)(1−tv)) = det(1−tu)·det(1−tv)`); §6 (pp. 78–79): Fredholm resolvent, Prop 10 + Lemme 3 (`|v_m| ≤ r₁⋯r_m`); §7 (pp. 80–82): Prop 11 (invertibility ⟺ `H(a) ≠ 0`), Prop 12 (Riesz decomposition; we extract only its eigenvector content). |
| `[Buz07]` | K. Buzzard, *Eigenvarieties*, LMS Lecture Notes 320 (2007), §3 pp. 20–24 | Divided-derivative (`Δˢ`) treatment of zero-of-order-`h` (p. 22), Prop 3.2 (p. 23) = Serre Prop 12 over Noetherian Banach algebras. Template for the ring-level statements. |
| `[Bel]` | Bellaïche, *The Eigenbook*, draft §II.2 | The repo's declared "Riesz theory" TODO (`Tate.lean:151`); we take the lighter Serre route rather than his resultants. |
| `[Kob84]` | Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58, Ch. IV §4 | The Newton-polygon ⇒ zeros half of the slope story (p-adic Weierstrass preparation). **Koblitz does not contain the operator-eigenvalue statement** — recorded here because the user half-remembered it; the operator statement is Serre's. |

## Mathlib / repo inventory (verified 2026-08-04 by exhaustive Explore pass)

| Concept | Status | Action |
| --- | --- | --- |
| `charPowerSeries`, `charCoeff`, minors, Hadamard bound `norm_minor_le_prod`, entireness, `norm_charCoeff_sub_le`, `charCoeff_eq_det_coeff`, `charPowerSeries_comm/conj` | `PhD/TateFredholm/Fredholm.lean` | USE (import) |
| Operator norm, `exists_lim_of_cauchySeq`, Neumann `exists_inverse_of_norm_id_sub_lt_one`, `opNorm_mul_le` etc. | `OperatorNorm.lean` | USE. **No normed-instance / tsum framework on `M →L[R] N` (deliberate)** → new `IsOpLimit` mini-API |
| `IsCompactoid`, `rowNorm`, truncations, `tendsto_truncation_comp`, `comp_left/right` | `Matrix.lean` | USE. Closure under `+`/`−`/`•`/`0`: **ABSENT** → new leaves |
| `summable_of_tendsto_cofinite`, `norm_tsum_le_iSup`, `bddAbove_range_norm_of_tendsto_cofinite` | `Tate.lean` | USE (scalar tsums only) |
| `PowerSeries.IsRestricted` (project version), `Restricted R c` subtype, Gauss norm `NormMulClass (Restricted R c)`, `IsMulDistinguished`, `weierstrassDivision_exists_of_isMulDistinguished` | `PhD/ForMathlib/RingTheory/PowerSeries/Restricted/…` | USE for the field-case finite-order step |
| Evaluation of a power series at a point (normed) | mathlib has only adic `PowerSeries.eval₂` (`IsLinearTopology`); ForMathlib: none | DEFINE `evalT a f := ∑' n, coeff n f * a ^ n` + API |
| Hasse/divided derivative on `PowerSeries` | mathlib: `Polynomial.hasseDeriv` only (+`hasseDeriv_mul`); PowerSeries: absent | DEFINE `PowerSeries.hasseDeriv` (coefficient formula mirror) + linear-factor product rule only |
| Cauchy product of tsums, nonarch | `Summable.tsum_mul_tsum`, `…_eq_tsum_sum_antidiagonal` (generic, product-summability as hypothesis) — mathlib | USE; product summability from the cofinite criterion (finite×finite bad set) |
| `Matrix.adjugate`, `adjugate_apply`, `mul_adjugate`; `Matrix.det_smul`, `det_mul` | mathlib | USE in the resolvent finite case and multiplicativity finite case |
| `ext_matrixCoeff` | `PhD/Jacobs/BlockOp.lean:115` | Do **not** import Jacobs (other board's files); restate privately if needed |

## Route (why this decomposition)

Serre §6–§7, specialised to the eigenvector statement:

1. **Resolvent** `P(t,u) = det(1−tu)/(1−tu) = Σ vₘ tᵐ`, `vₘ = Σ_{k≤m} cₖ u^{m−k}`
   (recursion `vₘ = cₘ·1 + u∘vₘ₋₁`). Entireness `‖vₘ‖Mᵐ → 0` via Serre's Lemme 3
   (`|vₘ| ≤` products of distinct row norms), proved by his 3-step route
   (finite case via adjugate/Cramer, row-supported case, truncation limit), with the
   repo's threshold-split (`δ/D/b`) replacing the sorted sequence.
2. **Divided evaluations** `Nₛ := (Δˢ P)(a,u)` (operator limits) and the equations
   `(1−a•u)∘Nₛ = u∘Nₛ₋₁ + (ΔˢH)(a)·1` (coefficientwise Pascal identity + limit).
3. **Multiplicativity of the determinant value** (Serre Prop 7 Cor 1, at `t = 1`):
   `D(u ⊞ v) = D(u)·D(v)` for `1−(u⊞v) = (1−u)(1−v)`, by truncation + finite
   `Matrix.det_mul` + a uniform coefficient-difference engine (replacing Serre's
   "réduisant modulo 𝔞").
4. **Prop 11**: `IsUnit (1 − a•u) ↔ IsUnit (evalT a H)` — `⟸` from `N₀` as a
   right inverse (+ commuting); `⟹` from multiplicativity applied to the inverse.
5. **Dichotomy** (the eigenvector): if `a` is a zero of finite order `h ≥ 1`
   (`ΔˢH(a) = 0` for `s < h`, `ΔʰH(a)` a unit) and `1−a•u` were injective, the
   equations force `N₀ = ⋯ = N_{h−1} = 0` and then `(1−a•u)∘N_h = ΔʰH(a)·1`, so
   `1−a•u` is invertible — contradicting Prop 11 `⟹` and `H(a) = 0`. Hence
   `ker (1−a•u) ≠ 0`.
6. **Field input** (the only field-specific leaf): every zero of a nonzero entire series
   over `K` has finite order — by iterated Weierstrass *division* by the distinguished
   linear factor `1 − a⁻¹X` (ForMathlib), with termination from Gauss-norm
   multiplicativity (`‖H_s‖ = ‖H‖·(‖a‖/c)ˢ < 1` eventually, versus constant
   coefficient 1 forcing `‖H_s‖ ≥ 1`).

Steps 1–5 are carried out over a general Banach–Tate ring `R` (matching the repo's
philosophy and strictly generalising Buzzard's Noetherian-Banach-algebra base); step 6
and the headline are over `K`.

## File structure

- `PhD/TateFredholm/Riesz.lean` — everything (single new file, ~1.1k lines expected).
  Imports: `PhD.TateFredholm.Fredholm`,
  `PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassDivision` (+ its
  GaussNorm dependency), mathlib `Polynomial.HasseDeriv` (for name-parallel API only),
  `Matrix.Adjugate`.
  Internal sections: OpLimit infrastructure → compactoid closure → `hasseDeriv` →
  `evalT` → resolvent → determinant value + multiplicativity → Riesz theorems → field
  corollaries.

## Generality decisions

- Machinery over `R : NormedCommRing + IsUltrametricDist + CompleteSpace + NormOneClass`
  with `[IsTate R]` per-theorem — identical to `Fredholm.lean`; `a : R` arbitrary;
  "zero of order `h`" via `IsUnit (ΔʰH(a))` (Buzzard p. 22's ring-level definition).
- The eigenvector dichotomy concludes `∃ x ≠ 0, (1 − a•u) x = 0` over `R`; the
  `u x = a⁻¹ • x` phrasing and the *existence* of a finite order require the field.
- No `Noetherian`, no `HasPr`: everything on the model space `c(I, R)`; one final
  corollary transports along `IsONable` via `charPowerSeries_conj`.
- New defs kept to four (`hasseDeriv`, `evalT`, `resolventCoeff`, `IsOpLimit`), each
  with API; everything else is `exists_`-phrased to match the repo's
  no-instances-on-operators design.

## Extension (2026-08-04, user-approved): full Riesz decomposition

Serre Prop. 12 in full: T021–T024 (Tier 1: projectors `p = eʰ` from Serre p. 81's
`e/f`-split, kernel/range characterisations, `IsTopCompl`, uniqueness, `dim N < ∞`)
and T025–T030 (Tier 2: `dim N(a) = h` via block conjugation — discreteness hypothesis
`hd` as in `isPotentiallyONable_of_uniformizer` — nilpotent-block determinant, local
Serre-Lemme-2, order uniqueness; MILESTONE-2 `exists_riesz_decomposition`). The
general-`K` (non-discrete) version of Tier 2 would need the `(Pr)`-level determinant
definition (the `§II.1.6` endgame) — deliberately out of scope, recorded.

## Dependency graph

```
T001 (IsOpLimit) ──┬─→ T007 (N_s exists) ─→ T008 (equations) ─→ T012 (dichotomy) ─→ T015 (field headline)
T002 (compactoid ±•)│                                     ↗ T011 (Prop 11) ↗
T003 (hasseDeriv) ──┼─→ T008                              │
T004 (evalT) ───────┼─→ T009 (D-value, scaling) ─→ T010 (multiplicativity) ─→ T011
T005 (resolventCoeff, finite case) ─→ T006 (bound+entire) ─→ T007
T013 (division step, field) ─→ T014 (finite order, field) ─→ T015 ─→ T016 (biconditional, ONable)

Extension:
T011,T012 ─→ T021 (projectors) ─→ T022 (ker/range/IsTopCompl) ─→ T023 (uniqueness)
T021,T022 ─→ T024 (dim N < ∞, field)          T025 (nilpotent det) ⊥  T026 (Lemme 2) ⊥ T027 (order unique)
T017,T018,T021–T026 ─→ T028 (H = ℓ^d·H') ─→ T029 (d = h) ─→ T030 (MILESTONE-2: Prop 12)
```
