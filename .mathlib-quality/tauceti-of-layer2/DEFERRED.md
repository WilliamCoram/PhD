# OverconvergentForms Layer 2 — planning paused (2026-10-06)

`/develop` for Layer 2 of `PhD/TauCeti/Roadmaps/OverconvergentForms/README.md` ("automorphic
functions and the spaces of forms", §§2.1–2.6, lines 699–831) was started and **paused by the user
after the survey**, before any skeleton was written. There is no Lean skeleton, no `plan.md`, no
`decomposition.md` and no `tickets.md`. This directory holds only this note, so `/develop`'s mode
detection will still treat the layer as a new project.

## Decisions taken by the user (2026-10-06)

1. **Wait for PFA Layer 2.** Layer 2's block model, orthonormalisability and property (Pr) clauses
   (§2.2.3, §2.5, §2.6, and §2.6.3's potential orthonormalisability) are phrased with the
   `p`-adic-functional-analysis Layer 2 objects: `C₀(I, K)`, the block equivalences, `Module.HasPr`,
   `Module.IsONable`, `Module.IsPotentiallyONable` and Serre's theorem. That layer was being planned
   in parallel on the board `.mathlib-quality/tauceti-pfa-layer2/`, with its skeleton in
   `PhD/TauCeti/Code/PadicFunctionalAnalysis/{ModelSpace/*,ONable,Orthogonal,Serre}.lean`, all
   lemmas still `sorry`. **Do not plan this layer until that board is finished.** Then state the
   block model and (Pr) directly in `C₀` form.
2. **§2.3.3 is left for later.** The disc models `A_{κ,s}` and Buzzard's level–radius trade
   (Proposition 11.1) need PFA §4.3, the disc model of locally analytic functions, which the chain
   does not have. Nothing else in Layer 2 depends on it. It has never been formalised in this repo:
   the legacy `PhD/Main/LWX/09_DiscModel.lean` has only the coefficient-level disc model for `ℤ_p`.
3. **§2.4.2 (loading the nebentypus) is undecided.** The user asked to be reminded of it when this
   board is next developed. The question: include it on this board, or defer it to Layer 3 where the
   diamond operators live. The planner's recommendation was to include it here. It is the
   `ε`-eigenspace of `S^D_{k,w}(U₁)` mapping into `S^D_{κ_ε}(U₀ ∩ U₀(𝔭^t))` for Layer 1's
   `Embeddings.classicalShape`. That is mostly group theory plus Layer 1 equivariance, about 8–10
   tickets.

## Survey results to reuse (so the next session need not redo them)

**Sources, verbatim locators** (text extracts in `.mathlib-quality/tauceti-of-layer1/references/`):
- Buzzard, *Eigenvarieties*, §9 pp. 68–69 (`buzzard.txt` ≈ lines 2700–2740): `Γ_λ := τ_λ⁻¹ D^× τ_λ ∩ U`;
  `(f|u)(g) := f(gu⁻¹).u_p`; `L(U, A) := {f : D^×\D_f^× → A : f|u = f ∀ u ∈ U}`; "the map
  `f ↦ (f(τ_λ))` induces an isomorphism `L(U, A) → ⊕ A^{Γ_λ}`. In particular, the functor `L(U, −)`
  is left exact."
- Buzzard §9 p. 70 (Definition of `S^D_{k,w}(U) = L(U, L_{n,v})`, "a finite-dimensional K-vector
  space"); §10 pp. 72–73 (`S^D_κ(U; r) := L(U, A_{κ,r})`; the sup norm `|f| = max_g |f(g)|` with the
  norm-preserving isomorphism onto `⊕ (A_{κ,r})^{Γ_λ}`; "`Γ_λ` acts on `A_{κ,r}` via a finite
  quotient. Hence `S^D_κ(U;r)` is a direct summand of an ONable Banach `O(X)`-module").
- Buzzard §11 pp. 73–75 (classical ⊆ overconvergent; loading the character `ε`); Proposition 11.1
  pp. 75–76 (`buzzard.txt` line 3057).
- Jacobs, thesis, Definition 1.30 and Lemma 1.31 (p. 19: `L(U; A) = {φ : φ(dgu) = φ(g)‖u_p}`,
  `L(U; A) = ⊕_i A^{Γ_i}`, "an easy check that the map `φ ↦ (φ(c_i))` is an isomorphism"); Theorem 2.1
  and Lemma 2.2 (p. 24: the three representatives of `U₁(9)`, "`Γ_i = {1}` for all `i = 0, 1, 2`").

**Existing API to state against** (full report of the Layer 0 inventory; names verified):
- `AdelicAlgebra.Dfx F D`, `globalUnits F D`, `classSet F D U` (Mathlib `DoubleCoset.Quotient`),
  class `HasFiniteClassSets F D` with `finite_classSet`, `IsCompleteFamily c U`, `IsSection c U`,
  `isSection_iff`, `exists_isSection`, `stabilizer c U` (carrier `u ∈ U ∧ c * u * c⁻¹ ∈ globalUnits`),
  `globalStabilizer`, `stabilizerEquiv`, `stabilizer_mul`, `finite_stabilizer` (definite, over `ℚ`),
  `unitsIncl_algebraMap_mem_stabilizer` (all `Level/ClassSet.lean`). Levels are plain
  `Subgroup (Dfx F D)` with separate `IsOpen`/`IsCompact` hypotheses; `U0`, `U0Level`, `U1Level`,
  `standardLevel`, `lowerRightResidueLevel` (`Level/Standard.lean`); `wildMonoid`, `wildMonoidOf`,
  `HasWildLevel`, `hasWildLevel_U0Level`, `isHeckeTriple_wildMonoidOf`, `heckeElement`
  (`Level/HeckePair.lean`); `toMatrix`, `toGL`, `unitAt`, `RigidificationAt` (`≃ₐ[F_v]`) in
  `Adelic/Components.lean`; every file opens `open scoped AdelicAlgebra.RightAlgebra`.
- Hamilton: `classRep : Fin 3 → Dfx ℚ ℍ[ℚ]`, `isSection_classRep`, `stabilizer_classRep i = ⊥`,
  `card_classSet_U1_9 = 3`, `subsingleton_classSet_U0`, `card_units_hurwitzOrder = 24`,
  `Hamilton.hasFiniteClassSets`, `U1_9`, `U0`.
- Layer 1: `WeightData.comap` (its docstring says "Layer 2 pulls the action back along
  `θ_𝔭 : Δ_t → S`"), `WeightData.pi`/`single`, `kappaSlashAction` (a `def`, use `letI`, needs
  `[CharZero K]` for `AnalyticWeight`), `norm_kappaSlash_apply_le`, `classicalAction`,
  `toTate_classicalAction`, `polySubmodule_stable`, `finrank_symPow`, `kappaSlash_smul_one`,
  `eq_zero_of_kappaSlash_eq_self_of_ne_one`. Coefficients: `MvPowerSeries.Restricted K (1 : ι → ℝ)`
  (complete, ultrametric; RAG proves `isOrthonormalBasis_monomial`).
- **Gap to fill first:** there is no monoid map `θ_𝔭 : ↥(wildMonoid …) →* ↥(SigmaNorm (v.adicCompletion F) …)`;
  build it from `mem_monoidM_iff_mem_sigmaNorm` (`Weight/Dictionary.lean`) and
  `valued_pow_eq_levelThreshold`. Mathlib's `NormedField (adicCompletion K v)` is
  `Valued.toNormedField _ ℤᵐ⁰`, so it agrees with Layer 1's dictionary.
- Mathlib to reuse: `DoubleCoset.Quotient`/`mk`/`rel_iff`; `lp (fun _ : G ↦ A) ∞` (sup norm
  `norm_eq_ciSup`, complete) as the canonical Banach home of bounded level functions;
  `Representation.averageMap` with `isProj_averageMap` (finite group, `[Invertible (card : K)]`) for
  the averaging projector of §2.6.2, applied to the **finite image** of `Γ_λ` (not to `Γ_λ`, which is
  infinite for `F ≠ ℚ`); `Submodule.ClosedComplemented`.

**Legacy code** (`PhD/Main/QMF/`, proof ideas only, cannot be imported): `01_AutomorphicFunction`,
`02_Decomposition` (`bijective_evalAtReps`, the inverse `f(g) := c(⟦g⟧) ∣ (p g).2` with one global
`choose`), `Slash/03_AutomorphicFunction` and `Slash/04_HeckeMatrix` (the right slash
`(φ ∣ δ)(g) = φ(g δ⁻¹) ∣ δ`, `evalAtRepsSlash`), `Weight/05_Forms`, `06_Compact`, `07_Fredholm`
(`transitionOp`), `08_Pr` (`stabAvg`, `stabProj`). Findings: the legacy code has **no sup norm or
isometry on forms** (all analysis was on the `c₀` model, transported algebraically); its (Pr)
assumes `[Fintype Γ_λ]`, valid only for `F = ℚ`; Buzzard's Proposition 11.1 is not formalised.

**Draft design reached before the pause** (not binding): `AutomorphicFunction G Γ A` as a structure
with `FunLike`, `Module R` for every `Module R A`, and the right slash as
`DistribMulAction Δᵐᵒᵖ (AutomorphicFunction G Γ A)` with `(op δ • φ) g = op δ • φ (g * δ⁻¹)`
(convention 2); `AutomorphicFunction.Level Γ R U hU` with `Γ` explicit and `hU : (U : Set G) ⊆ Δ`;
abstract `IsCompleteFamily`, `IsSection`, `stabilizerAt Γ U c := U ⊓ Γ.comap (MulAut.conj c)`
matching Layer 0's shapes by `Iff.rfl`; `evalAtReps`, the image `∏ A^{Γ_λ}` for a section, and the
sup norm through `lp ∞`. A scratch draft typechecked except for two trivial slips.
