# Development Plan: Newton polygons, Layer 0 (convex minorants and the polygon of a sequence)

Board: `.mathlib-quality/tauceti-np-layer0/` (named; the default board path belongs to another
agent's Newton-polygon work). Specification: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`,
Layer 0 (§0.1–§0.6) and its Examples. Code: `PhD/TauCeti/Code/NewtonPolygons/`, module prefix
`PhD.TauCeti.Code.NewtonPolygons`, never importing `PhD.Main.*` (CI-gated).

## Goal

The theory of the Newton polygon of an abstract point sequence `v : ℕ → WithTop ℝ`, stated with the
polygon *as its height function* (roadmap convention 1) and `⊤` as the only junk value (convention 5):

```lean
-- the specification (Basic.lean), on any discrete linear order ι — ℕ or ℤ
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
structure IsNewtonPolygonOf (v h : ι → WithTop ℝ) : Prop where
  convex : IsConvexSeq h
  le_points : ∀ k, h k ≤ v k
  greatest : ∀ g, IsConvexSeq g → (∀ k, g k ≤ v k) → ∀ k, g k ≤ h k

-- the polygon, as the greatest convex minorant
noncomputable def newtonPolygon (v : ι → WithTop ℝ) (k : ι) : WithTop ℝ :=
  ⨆ g : {g : ι → WithTop ℝ // IsConvexMinorant v g}, g.1 k

theorem IsNewtonPolygonOf.unique : IsNewtonPolygonOf v h → IsNewtonPolygonOf v g → h = g   -- proved
theorem isNewtonPolygonOf_newtonPolygon : (∃ g, IsConvexMinorant v g) → IsNewtonPolygonOf v (newtonPolygon v)
theorem exists_isNewtonPolygonOf_iff : (∃ h, IsNewtonPolygonOf v h) ↔ ∃ g, IsConvexMinorant v g
-- on ℕ: admissibility is that condition, and its failure is the vertical case
theorem exists_isNewtonPolygonOf_iff_isAdmissible {v : ℕ → WithTop ℝ} : (∃ h, IsNewtonPolygonOf v h) ↔ IsAdmissible v
def IsVertical (v : ℕ → WithTop ℝ) : Prop := (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v
```

together with: convex sequences (§0.1), the vertex walk proven equal to `newtonPolygon` by
uniqueness (§0.3), vertices / segments / slope multiset / purity / first break / truncation (§0.4),
supporting lines, the competitor lemma, faces and `SlopesUnbounded` (§0.5), Minkowski sums with the
subgradient property, additive faces and the unique minimising split (§0.6), and the roadmap's
worked examples.

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 0 | the specification; every milestone is a numbered clause there |
| [Ked07] | K. S. Kedlaya, *p-adic differential equations*, 18.787 (MIT, fall 2007), unit "Newton polygons", §§1–2; text extracted to the scratchpad (`kedlaya.txt`) | definition as lower convex hull (= intersection of halfplanes above nonvertical lines, i.e. the supremum of affine minorants); slope multiset; `v_r` as supporting-line intercept; Prop. 1 (Robba) inequality (1) and the unique-minimiser sentence; Cor. 2 face-endpoint sentence |
| [Kob84] | N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Ch. IV §3 p. 97 | vertices: "the points `(i_j, ord_p a_{i_j})` where the slopes change" (quoted in the source project's `Face.lean`) |
| [Mathlib] | `Analysis/Convex/Slope.lean`, `Analysis/Convex/Function.lean` (`ConvexOn.sup`) | the `ConvexOn` bridge and the "max of convex is convex" fact |
| [SRC] | `PhD/Main/NewtonPolygons/{Height,Spec,SpecConstruction,Face,Support,OfSlopes,Product}.lean`, `PhD/Main/ForMathlib/NumberTheory/NewtonPolygon/{Basic,Construction}.lean` at commit `fdc44e2` | **read-only reference for proof ideas** (sorry-free, machine-checked, different presentation). Never imported. Cited per leaf as "[SRC] File.decl". |

The user's instruction (2026-09-12): design follows the roadmap; [SRC] is consulted for proofs, not
ported or mirrored.

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---|---|---|
| Convex functions on a real set | `ConvexOn`, `ConvexOn.slope_mono_adjacent`, `convexOn_of_slope_mono_adjacent`, `ConvexOn.sup` | BRIDGE (§0.1.4); the `ℕ`-indexed theory is not a corollary and is built here |
| Lower convex hull of a discrete point set / greatest convex minorant | absent | DEFINE `IsConvexSeq`, `IsNewtonPolygonOf`, `newtonPolygon` |
| Supremum in `WithTop ℝ` | `le_ciSup (OrderTop.bddAbove _)`, `ciSup_le` (needs `Nonempty`) — verified by elaboration | USE; the family of convex minorants is nonempty under admissibility |
| Order-connected sets | `Set.OrdConnected`, `.out` | USE for the finiteness-interval condition |
| Finite infimum | `Finset.inf`, `Finset.inf_le`, `Finset.le_inf`, `Finset.exists_mem_eq_inf`, `Finset.inf_image` | USE for `minkowski` |
| `sInf` on `ℕ` | `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.sSup_mem` | USE for faces and the walk |
| `WithTop` arithmetic | `WithTop.coe_add`, `coe_nsmul`, `coe_le_coe`, `coe_lt_top`, `add_top`, `untop₀`, `coe_untop₀_of_ne_top` | USE |
| Multisets | `Multiset.range`, `count_map`, `card_map`, `replicate` | USE for the slope multiset |
| Newton polygon (any sense) | absent from Mathlib | DEFINE (this layer) |

## File structure (as for a Tau Ceti PR; Tau Ceti home noted in each module docstring)

| File | Roadmap | Tau Ceti home | Contents |
|---|---|---|---|
| `ConvexSeq.lean` | §0.1 | `TauCeti/Analysis/Convex/Sequence.lean` | generic over `ι`: `unitSlope`, `finiteSet`, `IsConvexSeq`, midpoint form, chord inequality, telescoping, steepening, sup/max of convex, asymptotics; on `ℕ`: affine sequences, `affineFrom`, min counterexample, `ConvexOn` bridge |
| `Basic.lean` | §0.2 | `TauCeti/NumberTheory/NewtonPolygon/Basic.lean` | generic over `ι`: `IsConvexMinorant`, `IsNewtonPolygonOf` (three fields), uniqueness (proved), `newtonPolygon` (sup), existence ↔ a convex minorant exists; on `ℕ`: `slopeTo`, `slopeSet`, `IsAdmissible` and its characterisations, anchoring theorems, `IsVertical`, invariances |
| `Int.lean` | §0.2.6 | `TauCeti/NumberTheory/NewtonPolygon/Int.lean` | `extendTop` and the reduction `newtonPolygon (extendTop v) = extendTop (newtonPolygon v)`; existence on `ℤ` ↔ the points lie above a line; the `-|k|` counterexample to the pointwise condition |
| `Slope.lean` | §0.4 | `.../Slope.lean` | `anchor`, `IsVertex`, `IsSegment`, `slopeIndices`, `slopeMultiset`, `IsPure`, `HasFirstBreak`, `truncate` |
| `Face.lean` | §0.5 | `.../Face.lean` | supporting-line and competitor lemmas, `twoSlope`, `SlopesUnbounded`, `faceLeft`/`faceRight` and their geometry |
| `Minkowski.lean` | §0.6 | `.../Minkowski.lean` | `minkowski`, convexity, subgradient, additive faces, unique minimiser, `slopeMultiset_minkowski` |
| `Construction.lean` | §0.3 | `.../Construction.lean` | `achievingSet`, `nextVertex`, `vertexSeq`, `lastVertex`, `vertexWalk`, spec proof, `vertexWalk_eq_newtonPolygon`, terminal behaviours, finite support |
| `Examples.lean` | Examples | (tests) | the worked examples as theorems |

Import graph: `ConvexSeq ← Basic ← {Slope ← {Face ← Minkowski, Construction} ← Examples, Int}`.
`Construction` and `Int` are leaves of the graph: nothing in §0.4–0.6 depends on the walk or on `ℤ`.

## Dependency graph (by ticket group)

```text
G1 ConvexSeq (§0.1) ──→ G2 Basic spec+sup (§0.2) ──→ G3 Slope (§0.4) ──→ G4 Face (§0.5) ──→ G5 Minkowski (§0.6)
                                                   └──→ G6 Construction (§0.3)  [independent of G4, G5]
G7 Examples: after G3 (most), G5 and G6 (the ray example)
G8 Int (§0.2.6): after G2 only   [independent of G3–G7]
```

## Generality and design decisions (binding for the tickets)

1. **Height function primary** ([RM] convention 1). No structure bundles slopes/lengths; `unitSlope`,
   `IsVertex`, `faceLeft`/`faceRight`, `slopeMultiset` are all derived from `h : ℕ → WithTop ℝ`.
   Consequence: uniqueness is literal equality (`IsNewtonPolygonOf.unique` is antisymmetry of
   `greatest`), and the prior B2 on `unitSlope_cases` (a phantom zero-width real-sloped segment,
   `b2_log.jsonl` 2026-08-03) cannot recur — there is no segment data to be inconsistent.
2. **`⊤` is the only junk value** ([RM] convention 5). `unitSlope h j = ⊤` iff `h j = ⊤ ∨ h (j+1) = ⊤`;
   no `⊥`, no `WithBotTop`. Consequence: the maximality field `greatest` quantifies over *all*
   convex minorants with no anchoring restriction — a competitor finite left of the anchor is
   harmlessly `≤ ⊤` there. ([SRC] `Spec.lean` needed the anchoring restriction precisely because
   its heights were `⊥` there.)
3. **Convexity is stated on the finiteness interval**: `IsConvexSeq h := (finiteSet h).OrdConnected ∧
   MonotoneOn (unitSlope h) (finiteSet h)`. Global `Monotone (unitSlope h)` is **false** whenever the
   anchor is past `0` (the unit slopes run `⊤, …, ⊤, s₀, s₁, …`); the prototype `Suggested.lean`
   got this wrong and is corrected here. The midpoint form is an equivalent characterisation given
   order-connectedness (`isConvexSeq_iff_midpoint`); alone it admits gaps of length ≥ 2
   (`(0, ⊤, ⊤, 0)` is midpoint-convex), which is why both fields are needed.
4. **`newtonPolygon` is the supremum of all convex minorants**, literally [Ked07]'s "intersection of
   every closed halfplane lying above some nonvertical line containing all the points" (with convex
   minorants in place of affine ones; the supporting-line lemma §0.5.1 shows the two families have
   the same supremum). `WithTop ℝ` supports this: `le_ciSup (OrderTop.bddAbove _)` and `ciSup_le`
   elaborate. Existence is then four short facts (sup of convex is convex; `≤ v`; `le_ciSup`; anchor
   and `⊤`-left-of-anchor via admissible and steepened lines), and the vertex walk is a theorem
   (`vertexWalk_eq_newtonPolygon`), not the definition. Junk: for inadmissible `v` the family is
   empty and the value is `sSup ∅`; documented, never relied on.
5. **Faces are stated for polygons anchored at `0`** (`h 0 ≠ ⊤`): `faceLeft`/`faceRight` are `sInf`s
   of index sets, which coincide with the roadmap's "number of unit slopes `< σ` / `≤ σ`" exactly
   when the anchor is `0` (`faceLeft_eq_ncard`, `faceRight_eq_ncard`). Every polygon Layers 2–6
   produce is anchored at `0` (`coeff 0 = 1`); a general anchor is handled by translation. This
   matches [SRC] `Face.lean`, whose lemmas all assume `starting_point.1 = 0`.
6. **Namespace**: everything lives in `NewtonPolygon` ([RM] convention 10), including the
   polygon-independent convexity file — its Tau Ceti home is `Analysis/Convex/`, and a reviewer may
   prefer a neutral namespace there; flagged, not decided here.
7. **One conclusion per declaration**: `IsNewtonPolygonOf` has five single-conclusion fields; the
   only `↔` with a long right-hand side is `hasFirstBreak_iff` (one biconditional, its RHS is the
   roadmap's own three-clause characterisation). The collinear example was split into a `def` and
   three theorems.
8. **Generality**: values in `WithTop ℝ` throughout; no `Γ` (Layer 2 pushes `WithTop Γ` into
   `WithTop ℝ` along `e`, [RM] convention 4). The index type is generic in §0.1–§0.2: a discrete
   linear order `ι` with `[LinearOrder ι] [SuccOrder ι]`, plus `[IsSuccArchimedean ι]
   [LocallyFiniteOrder ι] [NoMaxOrder ι]` where proofs walk along successors or sum over intervals.
   `ℕ` and `ℤ` are instances (`Order.succ_eq_add_one`, `Nat.card_Ico`, `Int.card_Ico` make the generic
   statements read as the familiar ones). Everything that needs a first point (§0.3–§0.6) is on `ℕ`;
   `Int.lean` reduces left-bounded `ℤ`-indexed point sets to it. Decision of 2026-09-12, on the
   user's request, so that Laurent-series polygons (two rays) share the definition.
9. **The specification has three fields** (`convex`, `le_points`, `greatest`) and no anchoring
   field: uniqueness is antisymmetry of `greatest` and never used anchoring, and on `ℤ` there may be
   no first point. On `ℕ` the anchoring facts are theorems (`anchor_eq`, `eq_top_of_forall_eq_top`,
   `eq_top_of_forall_le`). Existence is `∃ g, IsConvexMinorant v g`, index-agnostic; on `ℕ` that is
   `IsAdmissible`, and on `ℤ` it is "the points lie above a single line" — the pointwise two-sided
   slope condition is insufficient (`-|k|`).
10. **The vertical case is named, not represented.** `IsVertical v := (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v`.
    No `⊥` height: encoding the vertical line as `(v 0, ⊥, ⊥, …)` would make convex minorants
    three-valued and reintroduce the junk-ordering rules behind the 2026-08-03 B2; `IsVertical` gives
    every statement the object would (Layer 4: radius of convergence `0 ↔ IsVertical`).
11. **The terminal ray is named**: `EndsInRay h m` (unit slopes eventually the constant `m`), in
    `Slope.lean`, with its slope characterisation, the `SlopesUnbounded` trichotomy (`Face.lean`) and
    the walk detecting it in both directions (`Construction.lean`). It is the hypothesis Layer 4's
    ray case (§4.3.2) consumes. Decision of 2026-09-12, on the user's request.

## Build and verification protocol

- Skeleton gate: `lake build PhD.TauCeti.Code.NewtonPolygons.Examples
  PhD.TauCeti.Code.NewtonPolygons.Int` must succeed with `sorry` warnings only (`Examples` imports
  every other file except the leaf `Int`).
- **Imports are minimal, per file** (2026-09-12, at the user's request): `import Mathlib` in
  `ConvexSeq.lean` made every file in the chain load all of Mathlib — 8684 build jobs and 135–280 s
  per file. With targeted imports it is 2045 jobs and ~3.5 s per file. Mathlib and Tau Ceti both
  require this, so it is not only a speed measure. When a new declaration needs a Mathlib lemma the
  file does not yet import, add the module that declares it (find it by `grep -rn` in
  `.lake/packages/mathlib/Mathlib/`). `Roadmaps/NewtonPolygons/Suggested.lean` keeps `import Mathlib`
  — it is a prototype naming every layer's API, outside the `Code` chain; build it only when touched.
  Prune redundant imports with `lake exe shake` at cleanup time.
- Import gate (CI): no `import PhD.Main.*` under `PhD/TauCeti/`, no `import PhD.TauCeti.*` under
  `PhD/Main/`.
- Each ticket: `lake build` of its module, then `#print axioms` on the declaration — only `propext`,
  `Classical.choice`, `Quot.sound`.
- `/beastmode` runs inline as the main agent (user preference, 2026-09-05), one ticket at a time.

## Outcome (2026-09-13) — LAYER 0 COMPLETE

All 59 tickets are `done`. The development is `PhD/TauCeti/Code/NewtonPolygons/{ConvexSeq, Basic,
Slope, Face, Minkowski, Construction, Int, Examples}.lean` (5 447 lines, 261 public declarations),
built by the new chain root `PhD/TauCeti.lean`.

Gates, all passing as of 2026-09-13:

| Gate | Result |
|------|--------|
| `lake build PhD.TauCeti` | 1 674 jobs, 0 errors, **0 warnings** |
| `sorry` | 0 (the roadmap's own `Suggested.lean` sketch keeps its 45 by design) |
| `lake exe runLinter` (all 8 modules) | passes |
| `#print axioms` (all 261 declarations) | `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx` |
| Docstrings | 261/261 |
| Line length / file length | ≤ 100 codepoints / ≤ 1 111 lines |
| Debug artefacts (`#eval`, `set_option`, `axiom`, bare `simp`) | 0 |
| CI | `lake build PhD.TauCeti` step added to `.github/workflows/build-project.yml` |

The milestones: T010 (§0.2 existence/uniqueness), T026 (§0.6 faces and slope multisets add),
T031 (§0.3 the walk IS the polygon), T038 (the terminal-ray trichotomy), T036 (ℤ via `extendTop`).

Next layer: run `/develop` for Layer 1 (§1, the valuation input `(v, e, b)` and `WithZero.negLog` /
`Valuation.addVal`, the user's Mathlib PRs #43578/#43580) on a NEW named board.
