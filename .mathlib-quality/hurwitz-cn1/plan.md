# Development Plan — hurwitz-cn1 (class number one for the Hurwitz order)

Board: `.mathlib-quality/hurwitz-cn1/` (parallel-boards repo — always name this board).

## Goal

Discharge the single remaining external `sorry` of the JacobsSlash fork:

```lean
theorem JacobsSlash.hClassNumberOne : HClassNumberOne
-- HClassNumberOne : Prop :=
--   ∀ g : Dfx ℚ D, ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U0, g = d * u
```

[Jacobs, Lemma 1.22 (1.4.4)]: `D_f^× = D^× · U₀(1)`.  The 2026-08-05 deferral to FLT's
`completed_units` is CANCELLED (user 2026-08-10: Kevin Buzzard wants the Hurwitz
material removed from FLT; FLT's own statement is a `sorry`, so there is nothing to
port).  Proof route = the classical replacement recorded as R-CN1
([Voight GTM 288]: 11.3.2 norm-Euclidean → 11.3.4 right ideals principal → 27.6.8
idelic dictionary), NOT the thesis's out-of-scope Jacquet–Langlands argument.

## Containment (user instruction 2026-08-10)

All new code lives in the contained subfolder **`PhD/JacobsSlash/CN1/`** (flat
namespace `JacobsSlash`, digit-prefix naming, guillemet module names).  Live-file edits
are confined to: the already-applied skeleton surgery (`U3/2_Level.lean` theorem
removal + pointer note, `U3/6_Matrix.lean` import), and the final integration ticket
T19 (docstring/PROGRESS rewrites).  Never import `PhD.Jacobs` (legacy).

## References

- Voight, *Quaternion algebras*, GTM 288 — local PDF `Desktop/Papers/Voight -
  Quaternion Algebras.pdf`.  §11.3 (pp. 169-170), §9.4-9.5 (pp. 143-146), §27.6
  (pp. 468-469), §28.1-28.2 (pp. 477-479).  Verbatim quotes per leaf in
  `decomposition.md`.
- Jacobs thesis — local PDF `Desktop/Papers/Jacobs - Slopes of Compact Hecke
  Operators.pdf`, Def. 1.20 + Lemma 1.22 + (1.4.4)-(1.4.7) (pp. 15-17).
- FLT repo (`/Users/nkw24xru/Desktop/Lean/FLT/`) — statement seams only:
  `FLT/Data/HurwitzRatHat.lean` (`canonicalForm`, `completed_units` — both `sorry`,
  file being dropped).  **Adele API pointers** (user: "adele api will exist in the FLT
  folder"): the ported layer `PhD/QMF/FLTstuff/DedekindDomain/FiniteAdeleRing/`
  {`TensorRestrictedProduct`, `BaseChange`, `TensorPi`}.lean holds the restricted-
  product tensor machinery (`lTensorEquivLeft` etc.); its packaged form needs
  `CommRing M`, so it is the FALLBACK, not the primary route (see decomposition.md,
  discharge-attack record).

## Mathlib inventory (all grep-verified in `.lake/packages/mathlib` 2026-08-10)

| Concept | Mathlib status | Our action |
|---|---|---|
| Rounding `\|x − round x\| ≤ 1/2` | `abs_sub_round` (Algebra/Order/Round.lean:193) | USE |
| `ℍ[ℚ]` division ring, `normSq` mult. | `Quaternion.instDivisionRing`, `map_mul normSq` | USE |
| Right ideals | `Semiring.toOppositeModule` (`Module Rᵐᵒᵖ R`, `op s • y = y*s`) + `Submodule.mem_span_singleton` | USE |
| Minimal norm element | `Nat.sInf_mem` | USE |
| Finite adeles | `IsDedekindDomain.FiniteAdeleRing = Πʳ v, [K_v, 𝓞_v]`; element structure `a.2`; `isUnit_iff`; `Support.finite` | USE |
| ℤ dense in `𝓞_w` | `HeightOneSpectrum.denseRange_algebraMap` (AdicValuation.lean:883) + valuation bookkeeping | COMPOSE (leaf L11) |
| `D ⊗ 𝔸_f` restricted-product equivalence | NOT in mathlib; FLTstuff version needs `CommRing` | AVOID — elementary induction (N2), FLTstuff as fallback |
| Local order coordinates | project `mem_hurwitzOrder_iff_coords`, `tmul_mem_localOrder`, `Subring.closure_induction` | COMPOSE (leaf L10) |

Project infrastructure consumed (all public, sorry-free, read 2026-08-10):
`U3/1_Hurwitz.lean` (hurwitzOrder, hnorm API, 24 units), `U3/2_Level.lean` (localOrder
+ membership API, U0, integralMatrices, `mem_hurwitzOrder_of_forall_local`,
`unitsIncl_mem_U0_iff`, `toLocal_unitsIncl`), `QMF/Quaternionic.lean` (Dfx, unitsIncl,
globalUnits, toLocal), `QMF/UpiElement.lean` (unitAt — not needed but adjacent).

## File structure and dependency graph

```
CN1/2_Euclidean.lean      (imports U3/1_Hurwitz)          L1 → L2 → L3
CN1/3_LocalApprox.lean    (imports U3/2_Level)            L9, L10; L11 → L12 → L13
CN1/3_AdeleIntegrality.lean (imports U3/2_Level)          L4, L5 → L6; L4+L6 → L7, L8
CN1/4_Dictionary.lean     (imports the three above)       L14 → L15; L16(L7,L10,L13,L14)
                                                          → L17(L3,L15,L16) → L18 → L19(L8,L18)
U3/6_Matrix.lean          (imports CN1/4_Dictionary)      consumer (already wired)
```

## Generality decisions

- Everything concrete at `ℚ`, `D = ℍ[ℚ]`, `hurwitzOrder` — per the tranche convention
  (this is the thesis's setting; the Euclidean argument is genuinely
  Hurwitz-specific: [V Example 11.3.8] shows it FAILS for the Lipschitz order).
- `L1` could generalise to `FloorRing` coordinate fields — recorded, not taken.
- Right ideals as `Submodule 𝓞ᵐᵒᵖ 𝓞` (mathlib convention), not a bespoke structure.
- Valuation smallness stated with `Valued.v` on completions (project house style),
  not ideal-divisibility — this is the L13 formulation fix (see decomposition.md).
- No topology anywhere: the dictionary is algebra + valuations only.

## Skeleton status

Written and `lake build`-verified 2026-08-10 (3581 jobs, 20 sorries, 0 errors).
`hClassNumberOne` now DECLARED in `CN1/4_Dictionary.lean` (moved from `U3/2_Level.lean`
at skeleton time; name `JacobsSlash.hClassNumberOne` unchanged; single consumer
`U3/6_Matrix.lean` rewired and building).

## Execution

Workers run via `/beastmode` on `.mathlib-quality/hurwitz-cn1/tickets.md`.  ChatGPT MCP
not configured this session — plan validated against the sources directly (two
planning-time catches recorded in decomposition.md).  `omega` over `lia`; run
`lake exe runLinter` per cleanup gates.
