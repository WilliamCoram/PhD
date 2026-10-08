# CompactOperators Layer 0 — planning deferred (2026-09-18)

`/develop` for Layer 0 of `PhD/TauCeti/Roadmaps/CompactOperators/README.md` was started and
**stopped by the user at the context-gathering stage**. Nothing was planned: there is no Lean
skeleton, no `decomposition.md`, no `plan.md`, no `tickets.md`. This directory holds only this note,
so `/develop`'s mode detection will still treat the layer as a new project.

## Why we stopped

1. **The floor does not exist in the Tau Ceti chain.** Layer 0's Dependencies paragraph
   (README §"Layer 0 … Dependencies") declares the `p`-adic-functional-analysis roadmap, Layers 0–2
   and §4.1, "all of it, as the floor". Layer 0 consumes, concretely:
   - §0.4 `PseudoUniformizer`, `NormedRing.IsTate`, the bridge lemma;
   - §1.1 the scoped operator norm, `‖u x‖ ≤ ‖u‖ ‖x‖`, the Neumann inverse (§1.1.5); §1.2.5; §1.3;
   - §2.1 `C₀(I, R)`, `single`, `eval`, reindexing, blocks (§2.1.4), and the
     `ContinuousConstSMul` / `SMulCommClass` instances over a normed ring;
   - §2.2 `IsONable`, `IsPotentiallyONable`, `HasPr`, §2.2.4; §2.4.1;
   - §2.6 `matrixCoeff`, `truncation`, §2.6.1 (rows a null family with supremum `‖u‖`), §2.6.3,
     §2.6.4 (approximating closed f.g. submodules), §2.6.5 (closedness over Noetherian rings);
   - §4.1 restricted series as `c₀(ℕ, R)`, the radius-`c` variant, substitution.

   `PhD/TauCeti/Code/` contains only `NewtonPolygons/` and `OverconvergentForms/`. The sorry-free
   originals live in `PhD/Main/TateFredholm/` (`00_Tate`, `01_OperatorNorm`, `02_Compact`,
   `03_ModelSpace`, `04_Matrix`, `04_TateAlgebra`, `05_Noetherian`, `05_GenFun`, `06_BlockOp`,
   `06_Pr`, `08_BlockMap`, `00_Compose`; about 5 000 lines), which this chain may not import
   (CI-gated), so the floor must be restated before a Layer 0 skeleton can even type-check.

   Options put to the user, none chosen — the decision was to wait:
   - a floor slice on this board (F-series tickets restating only what Layer 0 consumes, under PFA's
     names in `PhD/TauCeti/Code/PadicFunctionalAnalysis/`, ported from `PhD/Main/TateFredholm/`);
   - develop PFA Layers 0–2 first, as their own boards, then return here;
   - plan against a sorry'd `Floor.lean` interface (cannot finish sorry-free on its own).

2. **Roadmap erratum found.** §0.3.4 (the inclusions `LA_h → LA_{h+1}`, the Amice bases, `eval h` as
   `diag (⌊n/pʰ⌋!)`) cites PFA §4.3.2 and §4.4.4, which lie beyond the declared floor (Layers 0–2 +
   §4.1). Either the Dependencies paragraph must add PFA §§4.3–4.4, or §0.3.4 should be stated
   abstractly (it is §0.2.7 applied to a diagonal operator whose entries tend to `0`). Not edited —
   to be settled when the layer is resumed.

## To resume

Settle (1), then (2), then run `/develop` naming this board (`.mathlib-quality/tauceti-co-layer0/`).
